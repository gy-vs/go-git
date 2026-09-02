package git

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"

	"github.com/go-git/go-git/v6/plumbing"
	"github.com/go-git/go-git/v6/plumbing/filemode"
	"github.com/go-git/go-git/v6/plumbing/object"
	"github.com/go-git/go-git/v6/storage/memory"
)

type BlameIgnoreSuite struct {
	BaseSuite
}

func TestBlameIgnoreSuite(t *testing.T) {
	t.Parallel()
	suite.Run(t, new(BlameIgnoreSuite))
}

// blameTestRepo builds small repositories with a fixed commit graph, fixed
// authors and fixed commit times so that blame results (and object hashes)
// are fully deterministic. It can back the repository with either the memory
// or the filesystem storer.
type blameTestRepo struct {
	t       *testing.T
	r       *Repository
	dir     string // working tree directory, empty for memory storage
	commits map[string]plumbing.Hash
	when    time.Time
}

func newBlameTestRepo(t *testing.T, filesystem bool) *blameTestRepo {
	t.Helper()
	h := &blameTestRepo{
		t:       t,
		commits: make(map[string]plumbing.Hash),
		when:    time.Date(2020, 1, 1, 0, 0, 0, 0, time.UTC),
	}
	if filesystem {
		h.dir = t.TempDir()
		r, err := PlainInit(h.dir, false)
		require.NoError(t, err)
		h.r = r
	} else {
		r, err := Init(memory.NewStorage(), nil)
		require.NoError(t, err)
		h.r = r
	}
	return h
}

// commit creates a commit containing exactly the given files (path to
// contents), with the commits referenced by the parent labels as parents.
func (h *blameTestRepo) commit(label string, parents []string, files map[string]string) plumbing.Hash {
	h.t.Helper()
	st := h.r.Storer

	entries := make([]object.TreeEntry, 0, len(files))
	for path, content := range files {
		obj := st.NewEncodedObject()
		obj.SetType(plumbing.BlobObject)
		w, err := obj.Writer()
		require.NoError(h.t, err)
		_, err = w.Write([]byte(content))
		require.NoError(h.t, err)
		require.NoError(h.t, w.Close())
		blobHash, err := st.SetEncodedObject(obj)
		require.NoError(h.t, err)
		entries = append(entries, object.TreeEntry{
			Name: path,
			Mode: filemode.Regular,
			Hash: blobHash,
		})
	}

	// git trees store entries sorted by name; the files map iterates in
	// random order, so sort explicitly
	sort.Slice(entries, func(i, j int) bool { return entries[i].Name < entries[j].Name })
	tree := &object.Tree{Entries: entries}
	treeObj := st.NewEncodedObject()
	treeObj.SetType(plumbing.TreeObject)
	require.NoError(h.t, tree.Encode(treeObj))
	treeHash, err := st.SetEncodedObject(treeObj)
	require.NoError(h.t, err)

	parentHashes := make([]plumbing.Hash, 0, len(parents))
	for _, p := range parents {
		parentHashes = append(parentHashes, h.commits[p])
	}
	when := h.when.AddDate(0, len(h.commits), 0)
	sig := object.Signature{Name: "Alice", Email: "alice@example.com", When: when}
	c := &object.Commit{
		Author:       sig,
		Committer:    sig,
		Message:      label,
		TreeHash:     treeHash,
		ParentHashes: parentHashes,
	}
	commitObj := st.NewEncodedObject()
	commitObj.SetType(plumbing.CommitObject)
	require.NoError(h.t, c.Encode(commitObj))
	hash, err := st.SetEncodedObject(commitObj)
	require.NoError(h.t, err)
	h.commits[label] = hash

	require.NoError(h.t, st.SetReference(plumbing.NewHashReference(plumbing.NewBranchReferenceName("main"), hash)))
	require.NoError(h.t, st.SetReference(plumbing.NewSymbolicReference(plumbing.HEAD, plumbing.NewBranchReferenceName("main"))))
	return hash
}

// blameLine is the expected attribution of a single line.
type blameLine struct {
	commit     string
	ignored    bool
	unblamable bool
}

type blameExpectation struct {
	rev       string
	path      string
	ignoreRev []string
	lines     []blameLine
}

func (h *blameTestRepo) blame(t *testing.T, exp blameExpectation) (*BlameResult, []cliBlameLine) {
	t.Helper()
	ignoreRevs := make([]plumbing.Revision, 0, len(exp.ignoreRev))
	for _, label := range exp.ignoreRev {
		ignoreRevs = append(ignoreRevs, plumbing.Revision(h.commits[label].String()))
	}
	result, err := h.r.BlameWithOptions(&BlameOptions{
		Rev:        plumbing.Revision(h.commits[exp.rev].String()),
		Path:       exp.path,
		IgnoreRevs: ignoreRevs,
	})
	require.NoError(t, err, "BlameWithOptions failed")
	h.assertResult(t, result, exp)
	cli := h.blameCLI(t, exp)
	h.assertCLI(t, result, cli)
	return result, cli
}

func (h *blameTestRepo) assertResult(t *testing.T, result *BlameResult, exp blameExpectation) {
	t.Helper()
	require.Len(t, result.Lines, len(exp.lines), "unexpected number of blamed lines")
	for i, want := range exp.lines {
		got := result.Lines[i]
		require.Equal(t, h.commits[want.commit].String(), got.Hash.String(),
			"line %d: expected commit %s, got %s (text=%q)", i+1, want.commit, got.Hash.String()[:8], got.Text)
		require.Equal(t, want.ignored, got.Ignored,
			"line %d (text=%q): unexpected Ignored flag", i+1, got.Text)
		require.Equal(t, want.unblamable, got.Unblamable,
			"line %d (text=%q): unexpected Unblamable flag", i+1, got.Text)
	}
}

type cliBlameLine struct {
	hash       string
	ignored    bool
	unblamable bool
}

// blameCLI runs system git blame with the same ignore configuration and
// returns the attribution of each line. Returns nil when system git is not
// available or the repository is not on disk.
func (h *blameTestRepo) blameCLI(t *testing.T, exp blameExpectation) []cliBlameLine {
	t.Helper()
	if h.dir == "" {
		return nil
	}
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("system git not available")
		return nil
	}

	args := []string{
		"-C", h.dir,
		"-c", "blame.markIgnoredLines=true",
		"-c", "blame.markUnblamableLines=true",
		"blame",
	}
	for _, label := range exp.ignoreRev {
		args = append(args, "--ignore-rev", h.commits[label].String())
	}
	args = append(args, h.commits[exp.rev].String(), "--", exp.path)

	cmd := exec.Command("git", args...)
	cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "HOME="+t.TempDir())
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("git blame failed: %v\n%s", err, out)
	}

	var lines []cliBlameLine
	re := regexp.MustCompile(`^([\^*? ]*)([0-9a-f]+)`)
	for outLine := range strings.SplitSeq(strings.TrimRight(string(out), "\n"), "\n") {
		m := re.FindStringSubmatch(outLine)
		if m == nil {
			t.Fatalf("cannot parse git blame output: %q", outLine)
		}
		lines = append(lines, cliBlameLine{
			hash:       m[2],
			ignored:    strings.Contains(m[1], "?"),
			unblamable: strings.Contains(m[1], "*"),
		})
	}
	return lines
}

// blameCLIWithFile runs system git blame reading the ignored revisions from
// an ignore-revs file.
func (h *blameTestRepo) blameCLIWithFile(t *testing.T, rev, path, ignoreFile string) []cliBlameLine {
	t.Helper()
	if h.dir == "" {
		return nil
	}
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("system git not available")
		return nil
	}

	args := []string{
		"-C", h.dir,
		"-c", "blame.markIgnoredLines=true",
		"-c", "blame.markUnblamableLines=true",
		"blame",
		"--ignore-revs-file", ignoreFile,
		h.commits[rev].String(), "--", path,
	}
	cmd := exec.Command("git", args...)
	cmd.Env = append(os.Environ(), "GIT_CONFIG_NOSYSTEM=1", "HOME="+t.TempDir())
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("git blame --ignore-revs-file failed: %v\n%s", err, out)
	}

	var lines []cliBlameLine
	re := regexp.MustCompile(`^([\^*? ]*)([0-9a-f]+)`)
	for outLine := range strings.SplitSeq(strings.TrimRight(string(out), "\n"), "\n") {
		m := re.FindStringSubmatch(outLine)
		if m == nil {
			t.Fatalf("cannot parse git blame output: %q", outLine)
		}
		lines = append(lines, cliBlameLine{
			hash:       m[2],
			ignored:    strings.Contains(m[1], "?"),
			unblamable: strings.Contains(m[1], "*"),
		})
	}
	return lines
}

func (h *blameTestRepo) assertCLI(t *testing.T, result *BlameResult, cli []cliBlameLine) {
	t.Helper()
	if cli == nil {
		return
	}
	require.Len(t, cli, len(result.Lines), "git and go-git disagree on the number of lines")
	for i, line := range result.Lines {
		want := cli[i]
		if !strings.HasPrefix(line.Hash.String(), want.hash) {
			t.Errorf("line %d: go-git blames %s but git blames %s (text=%q)", i+1, line.Hash.String()[:8], want.hash, line.Text)
		}
		require.Equal(t, want.ignored, line.Ignored,
			"line %d: Ignored flag differs from git (text=%q)", i+1, line.Text)
		require.Equal(t, want.unblamable, line.Unblamable,
			"line %d: Unblamable flag differs from git (text=%q)", i+1, line.Text)
	}
}

// writeIgnoreRevsFile writes an ignore-revs file containing the given commit
// labels, exercising blank lines and comments.
func (h *blameTestRepo) writeIgnoreRevsFile(t *testing.T, labels []string) string {
	t.Helper()
	var b strings.Builder
	b.WriteString("# ignored revisions\n")
	for _, label := range labels {
		b.WriteString("\n")
		b.WriteString("  " + h.commits[label].String() + "  # " + label + "\n")
	}
	content := b.String()
	if h.dir != "" {
		path := filepath.Join(h.dir, ".git-blame-ignore-revs")
		require.NoError(t, os.WriteFile(path, []byte(content), 0o644))
		return path
	}
	path := filepath.Join(t.TempDir(), "ignore-revs")
	require.NoError(t, os.WriteFile(path, []byte(content), 0o644))
	return path
}

func blameIgnoreRepos(t *testing.T) map[string]*blameTestRepo {
	return map[string]*blameTestRepo{
		"memory":     newBlameTestRepo(t, false),
		"filesystem": newBlameTestRepo(t, true),
	}
}

// TestBlameIgnoreReformat mirrors the basic git behaviour: unchanged lines
// keep their original author without marks, whitespace-only changes are
// traced back through the ignored revision (Ignored), genuinely new lines
// stay on the ignored revision (Unblamable), and later changes are attributed
// normally.
func (s *BlameIgnoreSuite) TestIgnoreRevsReformat() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"f.txt": "line one content here\nline two content here\nline three content here\n",
			})
			h.commit("c1", []string{"c0"}, map[string]string{
				"f.txt": "line one content here\n  line two content here\nline three content here\nbrand new line added in c1\n",
			})
			h.commit("c2", []string{"c1"}, map[string]string{
				"f.txt": "line one content here\n  line two content here\nline three content here\nbrand new line added in c1\nline five content here\n",
			})

			h.blame(t, blameExpectation{
				rev:       "c2",
				path:      "f.txt",
				ignoreRev: []string{"c1"},
				lines: []blameLine{
					{commit: "c0"},
					{commit: "c0", ignored: true},
					{commit: "c0"},
					{commit: "c1", unblamable: true},
					{commit: "c2"},
				},
			})
		})
	}
}

// TestIgnoreRevsConsecutive verifies that ignoring back-to-back revisions
// passes blame through every ignored revision.
func (s *BlameIgnoreSuite) TestIgnoreRevsConsecutive() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"f.txt": "the quick brown fox jumps over the lazy dog\npack my box with five dozen liquor jugs\n",
			})
			h.commit("c1", []string{"c0"}, map[string]string{
				"f.txt": "the quick brown fox jumps over the lazy dog\npack my box with five dozen liquor jugs\nextra line added in c1 content\n",
			})
			h.commit("c2", []string{"c1"}, map[string]string{
				"f.txt": "the quick brown fox jumps over the lazy dog\n  pack my box with five dozen liquor jugs\nextra line added in c1 content\n",
			})

			h.blame(t, blameExpectation{
				rev:       "c2",
				path:      "f.txt",
				ignoreRev: []string{"c1", "c2"},
				lines: []blameLine{
					{commit: "c0"},
					{commit: "c0", ignored: true},
					{commit: "c1", unblamable: true},
				},
			})

			// ignoring only the newest revision: the line added by c1 is
			// reached through an unchanged region, so no flag at all
			h.blame(t, blameExpectation{
				rev:       "c2",
				path:      "f.txt",
				ignoreRev: []string{"c2"},
				lines: []blameLine{
					{commit: "c0"},
					{commit: "c0", ignored: true},
					{commit: "c1"},
				},
			})
		})
	}
}

// TestIgnoreRevsRootAndNewFile covers the cases where an ignored revision
// cannot pass blame to a parent: a root commit and a revision introducing a
// new file. Git attributes the lines to the revision without flags.
func (s *BlameIgnoreSuite) TestIgnoreRevsRootAndNewFile() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"f.txt": "root line alpha content\nroot line beta content\n",
			})
			h.commit("c1", []string{"c0"}, map[string]string{
				"f.txt": "root line alpha content\nroot line beta content\nadded at c1\n",
			})

			// ignoring the root commit has no effect: there is no parent
			// to pass blame onto
			h.blame(t, blameExpectation{
				rev:       "c1",
				path:      "f.txt",
				ignoreRev: []string{"c0"},
				lines: []blameLine{
					{commit: "c0"},
					{commit: "c0"},
					{commit: "c1"},
				},
			})

			// a revision that introduces the blamed file: the lines stay
			// attributed to the ignored revision without marks
			h.commit("c2", []string{"c1"}, map[string]string{
				"f.txt":   "root line alpha content\nroot line beta content\nadded at c1\n",
				"new.txt": "brand new file line one\nbrand new file line two\n",
			})
			h.blame(t, blameExpectation{
				rev:       "c2",
				path:      "new.txt",
				ignoreRev: []string{"c2"},
				lines: []blameLine{
					{commit: "c2"},
					{commit: "c2"},
				},
			})
		})
	}
}

// TestIgnoreRevsRename checks blame across a rename, with the pure rename
// ignored and with the revision modifying the renamed file ignored.
func (s *BlameIgnoreSuite) TestIgnoreRevsRename() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"old.txt": "line one content data\nline two content data\nline three content data\n",
			})
			// pure rename, identical content
			h.commit("c1", []string{"c0"}, map[string]string{
				"new.txt": "line one content data\nline two content data\nline three content data\n",
			})
			h.commit("c2", []string{"c1"}, map[string]string{
				"new.txt": "line one content data!!\nline two content data\nline three content data\n",
			})

			// ignore the modifying revision: the changed line is traced
			// back to the renamed file in the parents
			h.blame(t, blameExpectation{
				rev:       "c2",
				path:      "new.txt",
				ignoreRev: []string{"c2"},
				lines: []blameLine{
					{commit: "c0", ignored: true},
					{commit: "c0"},
					{commit: "c0"},
				},
			})

			// ignore the pure rename: identical blob, everything is
			// attributed as in a normal blame
			h.blame(t, blameExpectation{
				rev:       "c2",
				path:      "new.txt",
				ignoreRev: []string{"c1"},
				lines: []blameLine{
					{commit: "c2"},
					{commit: "c0"},
					{commit: "c0"},
				},
			})
		})
	}
}

// TestIgnoreRevsMerge covers a merge commit and ignored commits on either
// side of the merge, plus a change on top of the merge.
func (s *BlameIgnoreSuite) TestIgnoreRevsMerge() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			base := map[string]string{
				"f.txt": "base line one content\nbase line two content\nbase line three content\n",
			}
			h.commit("c0", nil, base)
			h.commit("side", []string{"c0"}, map[string]string{
				"f.txt": "base line one content\nbase line two content\nbase line three content\nside added line content here\n",
			})
			h.commit("main", []string{"c0"}, map[string]string{
				"f.txt": "base line one content\nMAIN changed line two!!\nbase line three content\n",
			})
			// merge commit: main is the first parent, side the second
			h.commit("merge", []string{"main", "side"}, map[string]string{
				"f.txt": "base line one content\nMAIN changed line two!!\nbase line three content\nside added line content here\n",
			})
			h.commit("post", []string{"merge"}, map[string]string{
				"f.txt": "base line one content\nMAIN changed line two!!\nbase line three content\nside added line content here\nEVIL merge brand new line\n",
			})

			plain := []blameLine{
				{commit: "c0"},
				{commit: "main"},
				{commit: "c0"},
				{commit: "side"},
			}

			// ignoring the (clean) merge itself: nothing is marked
			h.blame(t, blameExpectation{
				rev:       "merge",
				path:      "f.txt",
				ignoreRev: []string{"merge"},
				lines:     plain,
			})

			// ignoring the side branch tip: its added line is matched
			// against the base through the heuristic
			h.blame(t, blameExpectation{
				rev:       "merge",
				path:      "f.txt",
				ignoreRev: []string{"side"},
				lines: []blameLine{
					{commit: "c0"},
					{commit: "main"},
					{commit: "c0"},
					{commit: "c0", ignored: true},
				},
			})

			// ignoring the main line commit: its changed line is matched
			// against the base
			h.blame(t, blameExpectation{
				rev:       "merge",
				path:      "f.txt",
				ignoreRev: []string{"main"},
				lines: []blameLine{
					{commit: "c0"},
					{commit: "c0", ignored: true},
					{commit: "c0"},
					{commit: "side"},
				},
			})

			// a line added on top of the merge, attributed to no parent,
			// is unblamable
			h.blame(t, blameExpectation{
				rev:       "post",
				path:      "f.txt",
				ignoreRev: []string{"post"},
				lines: append(append([]blameLine{}, plain...),
					blameLine{commit: "post", unblamable: true}),
			})
		})
	}
}

// TestIgnoreRevsParity ensures that without ignore configuration the result
// is identical to the plain Blame function and that the structured flags are
// only set when ignoring revisions.
func (s *BlameIgnoreSuite) TestIgnoreRevsParity() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"f.txt": "line one content here\nline two content here\n",
			})
			h.commit("c1", []string{"c0"}, map[string]string{
				"f.txt": "line one content here\nline two content here\nline three added now\n",
			})

			c, err := h.r.CommitObject(h.commits["c1"])
			require.NoError(t, err)

			plain, err := Blame(c, "f.txt")
			require.NoError(t, err)
			withOpts, err := h.r.BlameWithOptions(&BlameOptions{
				Rev:  plumbing.Revision(h.commits["c1"].String()),
				Path: "f.txt",
			})
			require.NoError(t, err)
			require.Equal(t, plain.Lines, withOpts.Lines)

			for _, line := range withOpts.Lines {
				require.False(t, line.Ignored)
				require.False(t, line.Unblamable)
			}

			// the package level function with full hashes matches the
			// repository method when revisions are ignored
			ignoredHash := h.commits["c1"]
			pkgResult, err := BlameWithOptions(c, &BlameOptions{
				Path:       "f.txt",
				IgnoreRevs: []plumbing.Revision{plumbing.Revision(ignoredHash.String())},
			})
			require.NoError(t, err)
			repoResult, err := h.r.BlameWithOptions(&BlameOptions{
				Rev:        plumbing.Revision(h.commits["c1"].String()),
				Path:       "f.txt",
				IgnoreRevs: []plumbing.Revision{plumbing.Revision(ignoredHash.String())},
			})
			require.NoError(t, err)
			require.Equal(t, repoResult.Lines, pkgResult.Lines)
		})
	}
}

// TestIgnoreRevsFile exercises reading the ignore list from a file with
// comments and blank lines.
func (s *BlameIgnoreSuite) TestIgnoreRevsFile() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"f.txt": "line one content here\nline two content here\nline three content here\n",
			})
			h.commit("c1", []string{"c0"}, map[string]string{
				"f.txt": "line one content here\n  line two content here\nline three content here\nbrand new line in c1\n",
			})
			ignoreFile := h.writeIgnoreRevsFile(t, []string{"c1"})

			result, err := h.r.BlameWithOptions(&BlameOptions{
				Rev:            plumbing.Revision(h.commits["c1"].String()),
				Path:           "f.txt",
				IgnoreRevsFile: ignoreFile,
			})
			require.NoError(t, err)
			require.Len(t, result.Lines, 4)
			require.Equal(t, h.commits["c0"], result.Lines[1].Hash)
			require.True(t, result.Lines[1].Ignored)
			require.Equal(t, h.commits["c1"], result.Lines[3].Hash)
			require.True(t, result.Lines[3].Unblamable)

			// the same ignore file drives system git --ignore-revs-file
			if cli := h.blameCLIWithFile(t, "c1", "f.txt", ignoreFile); cli != nil {
				h.assertCLI(t, result, cli)
			}
		})
	}
}

func (s *BlameIgnoreSuite) TestIgnoreRevsErrors() {
	for name, h := range blameIgnoreRepos(s.T()) {
		s.T().Run(name, func(t *testing.T) {
			h.commit("c0", nil, map[string]string{
				"f.txt": "line one content here\n",
			})
			h.commit("c1", []string{"c0"}, map[string]string{
				"f.txt": "line one content here\nline two content here\n",
			})

			// revision to blame cannot be resolved
			_, err := h.r.BlameWithOptions(&BlameOptions{
				Rev:  plumbing.Revision("no-such-revision"),
				Path: "f.txt",
			})
			require.Error(t, err)

			// ignored revision cannot be resolved
			_, err = h.r.BlameWithOptions(&BlameOptions{
				Rev:        plumbing.Revision(h.commits["c1"].String()),
				Path:       "f.txt",
				IgnoreRevs: []plumbing.Revision{"does-not-exist"},
			})
			require.Error(t, err)

			// path does not exist at the revision
			_, err = h.r.BlameWithOptions(&BlameOptions{
				Rev:  plumbing.Revision(h.commits["c1"].String()),
				Path: "no-such-file.txt",
			})
			require.Error(t, err)

			// ignore revs file does not exist
			_, err = h.r.BlameWithOptions(&BlameOptions{
				Rev:            plumbing.Revision(h.commits["c1"].String()),
				Path:           "f.txt",
				IgnoreRevsFile: filepath.Join(t.TempDir(), "missing"),
			})
			require.Error(t, err)

			// ignore revs file with an invalid object name
			badFile := filepath.Join(t.TempDir(), "ignores")
			require.NoError(t, os.WriteFile(badFile, []byte("# comment\nnot-a-hash\n"), 0o644))
			_, err = h.r.BlameWithOptions(&BlameOptions{
				Rev:            plumbing.Revision(h.commits["c1"].String()),
				Path:           "f.txt",
				IgnoreRevsFile: badFile,
			})
			require.Error(t, err)

			c, err := h.r.CommitObject(h.commits["c1"])
			require.NoError(t, err)

			// package level function rejects revision expressions
			_, err = BlameWithOptions(c, &BlameOptions{
				Path:       "f.txt",
				IgnoreRevs: []plumbing.Revision{"HEAD~1"},
			})
			require.Error(t, err)
		})
	}
}

// TestIgnoreRevsExpressions verifies that revision expressions (branch names,
// ancestry and abbreviated hashes) are accepted. Only meaningful on a
// repository with references, which is the filesystem backed one.
func (s *BlameIgnoreSuite) TestIgnoreRevsExpressions() {
	h := newBlameTestRepo(s.T(), true)

	h.commit("c0", nil, map[string]string{
		"f.txt": "line one content here\nline two content here\nline three content here\n",
	})
	h.commit("c1", []string{"c0"}, map[string]string{
		"f.txt": "line one content here\n  line two content here\nline three content here\nbrand new line in c1\n",
	})
	t := s.T()
	shortHash := h.commits["c1"].String()[:10]

	var result *BlameResult
	for _, ignore := range [][]plumbing.Revision{
		{"HEAD"},
		{plumbing.Revision(shortHash)},
	} {
		var err error
		result, err = h.r.BlameWithOptions(&BlameOptions{
			Rev:        "HEAD",
			Path:       "f.txt",
			IgnoreRevs: ignore,
		})
		require.NoError(t, err, "ignore %v failed", ignore)
		require.Len(t, result.Lines, 4)
		require.Equal(t, h.commits["c0"], result.Lines[1].Hash, "ignore %v", ignore)
		require.True(t, result.Lines[1].Ignored, "ignore %v", ignore)
		require.Equal(t, h.commits["c1"], result.Lines[3].Hash, "ignore %v", ignore)
		require.True(t, result.Lines[3].Unblamable, "ignore %v", ignore)
	}

	// the system git CLI agrees when using the same revision
	h.assertCLI(t, result, h.blameCLI(t, blameExpectation{
		rev:       "c1",
		path:      "f.txt",
		ignoreRev: []string{"c1"},
	}))
}
