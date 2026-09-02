package git

import (
	"bufio"
	"bytes"
	"container/heap"
	"errors"
	"fmt"
	"io"
	"maps"
	"os"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode/utf8"

	"github.com/sergi/go-diff/diffmatchpatch"

	"github.com/go-git/go-git/v6/plumbing"
	"github.com/go-git/go-git/v6/plumbing/object"
	"github.com/go-git/go-git/v6/utils/diff"
	"github.com/go-git/go-git/v6/utils/ioutil"
)

// BlameResult represents the result of a Blame operation.
type BlameResult struct {
	// Path is the path of the File that we're blaming.
	Path string
	// Rev (Revision) is the hash of the specified Commit used to generate this result.
	Rev plumbing.Hash
	// Lines contains every line with its authorship.
	Lines []*Line
}

// BlameOptions contains the options for a Blame operation.
type BlameOptions struct {
	// Rev is the revision at which to blame the file. It is only used by
	// Repository.BlameWithOptions and accepts hashes and revision
	// expressions such as branch names, tags or "HEAD~1".
	Rev plumbing.Revision
	// Path is the path of the File to blame, relative to the root of the
	// repository.
	Path string
	// IgnoreRevs lists revisions whose changes are ignored when assigning
	// blame, mirroring `git blame --ignore-rev`. When used with the package
	// level BlameWithOptions function the revisions must be full commit
	// hashes; Repository.BlameWithOptions also accepts revision expressions
	// such as branch names or "HEAD~1".
	IgnoreRevs []plumbing.Revision
	// IgnoreRevsFile is the path to a file listing revisions to ignore, one
	// per line; blank lines and lines starting with '#' are ignored.
	// Mirrors `git blame --ignore-revs-file`. The revisions must be full
	// commit hashes.
	IgnoreRevsFile string
}

// Blame returns a BlameResult with the information about the last author of
// each line from file `path` at commit `c`.
func Blame(c *object.Commit, path string) (*BlameResult, error) {
	return doBlame(c, path, nil)
}

// BlameWithOptions returns a BlameResult with the information about the last
// author of each line of the file given in the options at commit c. It
// behaves like Blame, but ignores the revisions in IgnoreRevs and
// IgnoreRevsFile when assigning blame, mirroring git's
// `--ignore-rev`/`--ignore-revs-file`.
//
// Lines that an ignored revision changed but that can be traced back to one
// of its parents are attributed to that parent and marked on the resulting
// Line with Ignored set to true (the lines git-blame marks with '?' when
// blame.markIgnoredLines is enabled). Lines introduced by an ignored revision
// that cannot be traced back to any parent stay attributed to that revision
// and are marked with Unblamable set to true (the lines git-blame marks
// with '*' when blame.markUnblamableLines is enabled).
//
// When used as a package level function the ignored revisions must be
// provided as full commit hashes. Repository.BlameWithOptions accepts
// revision expressions as well.
func BlameWithOptions(c *object.Commit, opts *BlameOptions) (*BlameResult, error) {
	if opts == nil {
		opts = &BlameOptions{}
	}

	ignoreRevs := make(map[plumbing.Hash]struct{})
	for _, rev := range opts.IgnoreRevs {
		hash := rev.String()
		if !plumbing.IsHash(hash) {
			return nil, fmt.Errorf("cannot ignore revision %q: expected a full commit hash; use Repository.BlameWithOptions to resolve revision expressions", hash)
		}
		ignoreRevs[plumbing.NewHash(hash)] = struct{}{}
	}
	if opts.IgnoreRevsFile != "" {
		hashes, err := parseIgnoreRevsFile(opts.IgnoreRevsFile)
		if err != nil {
			return nil, err
		}
		for _, hash := range hashes {
			ignoreRevs[hash] = struct{}{}
		}
	}

	return doBlame(c, opts.Path, ignoreRevs)
}

// parseIgnoreRevsFile reads an ignore-revs file containing one full commit
// hash per line. Blank lines and comments (lines starting with '#') are
// ignored, matching git's object name list parsing.
func parseIgnoreRevsFile(path string) ([]plumbing.Hash, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("could not open ignore revs file %s: %w", path, err)
	}
	defer ioutil.CheckClose(f, &err)

	var hashes []plumbing.Hash
	scanner := bufio.NewScanner(f)
	for scanner.Scan() {
		line := scanner.Text()
		if i := strings.IndexByte(line, '#'); i >= 0 {
			line = line[:i]
		}
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if !plumbing.IsHash(line) {
			return nil, fmt.Errorf("invalid object name in ignore revs file: %s", line)
		}
		hashes = append(hashes, plumbing.NewHash(line))
	}
	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("could not read ignore revs file %s: %w", path, err)
	}

	return hashes, nil
}

func doBlame(c *object.Commit, path string, ignoreRevs map[plumbing.Hash]struct{}) (*BlameResult, error) {
	// The file to blame is identified by the input arguments:
	// commit and path. commit is a Commit object obtained from a Repository. Path
	// represents a path to a specific file contained in the repository.
	//
	// Blaming a file is done by walking the tree in reverse order trying to find where each line was last modified.
	//
	// When a diff is found it cannot immediately assume it came from that commit, as it may have come from 1 of its
	// parents, so it will first try to resolve those diffs from its parents, if it couldn't find the change in its
	// parents then it will assign the change to itself.
	//
	// When encountering 2 parents that have made the same change to a file it will choose the parent that was merged
	// into the current branch first (this is determined by the order of the parents inside the commit).
	//
	// When a commit is in ignoreRevs the lines that would normally be blamed on it are instead passed to its
	// parents (mirroring git blame --ignore-rev): lines that match a parent are attributed to it (and flagged
	// ignored), lines that match no parent stay on the ignored commit flagged unblamable.
	//
	// This currently works on a line by line basis, if performance becomes an issue it could be changed to work with
	// hunks rather than lines. Then when encountering diff hunks it would need to split them where necessary.

	b := new(blame)
	b.fRev = c
	b.path = path
	b.ignoreRevs = ignoreRevs
	b.q = new(priorityQueue)

	file, err := b.fRev.File(path)
	if err != nil {
		return nil, err
	}
	finalLines, err := file.Lines()
	if err != nil {
		return nil, err
	}
	finalLength := len(finalLines)

	needsMap := make([]lineMap, finalLength)
	for i := range needsMap {
		needsMap[i] = lineMap{Orig: i, Cur: i, FromParentNo: -1}
	}
	contents, err := file.Contents()
	if err != nil {
		return nil, err
	}
	b.q.Push(&queueItem{
		Commit:   c,
		path:     path,
		Contents: contents,
		NeedsMap: needsMap,
	})
	items := make([]*queueItem, 0)
	for {
		items = items[:0]
		for {
			if b.q.Len() == 0 {
				return nil, errors.New("invalid state: no items left on the blame queue")
			}
			item := b.q.Pop()
			items = append(items, item)
			next := b.q.Peek()
			if next == nil || next.Hash != item.Commit.Hash {
				break
			}
		}
		finished, err := b.addBlames(items)
		if err != nil {
			return nil, err
		}
		if finished {
			break
		}
	}

	lineToCommit := make([]*object.Commit, finalLength)
	ignored := make([]bool, finalLength)
	unblamable := make([]bool, finalLength)
	for i := range needsMap {
		lineToCommit[i] = needsMap[i].Commit
		ignored[i] = needsMap[i].ignored
		unblamable[i] = needsMap[i].unblamable
	}

	lines := newLines(finalLines, lineToCommit, ignored, unblamable)

	return &BlameResult{
		Path:  path,
		Rev:   c.Hash,
		Lines: lines,
	}, nil
}

// Line values represent the contents and author of a line in BlamedResult values.
type Line struct {
	// Author is the email address of the last author that modified the line.
	Author string
	// AuthorName is the name of the last author that modified the line.
	AuthorName string
	// Text is the original text of the line.
	Text string
	// Date is when the original text of the line was introduced
	Date time.Time
	// Hash is the commit hash that introduced the original line
	Hash plumbing.Hash
	// Ignored is true when the line was changed by an ignored revision but
	// its authorship could be passed to one of that revision's parents.
	// This mirrors the lines git-blame marks with '?' when the
	// blame.markIgnoredLines configuration option is enabled.
	Ignored bool
	// Unblamable is true when the line was introduced by an ignored
	// revision but it could not be attributed to any of its parents, in
	// which case Hash is the ignored revision. This mirrors the lines
	// git-blame marks with '*' when the blame.markUnblamableLines
	// configuration option is enabled.
	Unblamable bool
}

func newLine(author, authorName, text string, date time.Time, hash plumbing.Hash) *Line {
	return &Line{
		Author:     author,
		AuthorName: authorName,
		Text:       text,
		Hash:       hash,
		Date:       date,
	}
}

func newLines(contents []string, commits []*object.Commit, ignored, unblamable []bool) []*Line {
	result := make([]*Line, 0, len(contents))
	for i := range contents {
		line := newLine(
			commits[i].Author.Email, commits[i].Author.Name, contents[i],
			commits[i].Author.When, commits[i].Hash,
		)
		if ignored != nil {
			line.Ignored = ignored[i]
		}
		if unblamable != nil {
			line.Unblamable = unblamable[i]
		}
		result = append(result, line)
	}

	return result
}

// this struct is internally used by the blame function to hold its
// inputs, outputs and state.
type blame struct {
	// the path of the file to blame
	path string
	// the commit of the final revision of the file to blame
	fRev *object.Commit
	// the hashes of commits whose changes are ignored when assigning blame
	ignoreRevs map[plumbing.Hash]struct{}
	// queue of commits that need resolving
	q *priorityQueue
}

type lineMap struct {
	Orig, Cur    int
	Commit       *object.Commit
	FromParentNo int
	// ignored is set when the line was attributed through an ignored
	// revision: an ignored revision changed the line, but it could be
	// traced back to one of its parents.
	ignored bool
	// unblamable is set when the line was introduced by an ignored
	// revision and it could not be traced back to any of its parents.
	unblamable bool
}

// ignoreHunk describes a contiguous changed region between a parent and the
// target commit, using 0-based line indexes in each file.
type ignoreHunk struct {
	startA, countA int // parent lines removed by the hunk
	startB, countB int // target lines added by the hunk
}

func (b *blame) addBlames(curItems []*queueItem) (bool, error) {
	curItem := curItems[0]

	// Simple optimisation to merge paths, there is potential to go a bit further here and check for any duplicates
	// not only if they are all the same.
	if len(curItems) == 1 {
		curItems = nil
	} else if curItem.IdenticalToChild {
		allSame := true
		lenCurItems := len(curItems)
		lowestParentNo := curItem.ParentNo
		for i := 1; i < lenCurItems; i++ {
			if !curItems[i].IdenticalToChild || curItem.Child != curItems[i].Child {
				allSame = false
				break
			}
			lowestParentNo = min(lowestParentNo, curItems[i].ParentNo)
		}
		if allSame {
			curItem.Child.numParentsNeedResolving = curItem.Child.numParentsNeedResolving - lenCurItems + 1
			curItems = nil // free the memory
			curItem.ParentNo = lowestParentNo

			// Now check if we can remove the parent completely
			for curItem.Child.IdenticalToChild && curItem.Child.MergedChildren == nil && curItem.Child.numParentsNeedResolving == 1 {
				oldChild := curItem.Child
				curItem.Child = oldChild.Child
				curItem.ParentNo = oldChild.ParentNo
			}
		}
	}

	// if we have more than 1 item for this commit, create a single needsMap
	if len(curItems) > 1 {
		curItem.MergedChildren = make([]childToNeedsMap, len(curItems))
		for i, c := range curItems {
			curItem.MergedChildren[i] = childToNeedsMap{
				Child:            c.Child,
				NeedsMap:         c.NeedsMap,
				OrigIndex:        c.OrigIndex,
				IdenticalToChild: c.IdenticalToChild,
				ParentNo:         c.ParentNo,
			}
		}
		newNeedsMap := make([]lineMap, 0, len(curItem.NeedsMap))
		newNeedsMap = append(newNeedsMap, curItems[0].NeedsMap...)

		for i := 1; i < len(curItems); i++ {
			cur := curItems[i].NeedsMap
			n := 0 // position in newNeedsMap
			c := 0 // position in current list
		curLoop:
			for c < len(cur) {
				switch {
				case n == len(newNeedsMap):
					newNeedsMap = append(newNeedsMap, cur[c:]...)
					break curLoop
				case newNeedsMap[n].Cur < cur[c].Cur:
					n++
				case newNeedsMap[n].Cur > cur[c].Cur:
					newNeedsMap = append(newNeedsMap, cur[c])
					newPos := len(newNeedsMap) - 1
					for newPos > n {
						newNeedsMap[newPos-1], newNeedsMap[newPos] = newNeedsMap[newPos], newNeedsMap[newPos-1]
						newPos--
					}
					n++
					c++
				default:
					// two needs at the same parent line position: keep
					// both, as they may belong to different child lines
					newNeedsMap = append(newNeedsMap, cur[c])
					newPos := len(newNeedsMap) - 1
					for newPos > n+1 {
						newNeedsMap[newPos-1], newNeedsMap[newPos] = newNeedsMap[newPos], newNeedsMap[newPos-1]
						newPos--
					}
					n += 2
					c++
				}
			}
		}
		curItem.NeedsMap = newNeedsMap
		curItem.IdenticalToChild = false
		curItem.Child = nil
	}

	parents, err := parentsContainingPath(curItem.path, curItem.Commit)
	if err != nil {
		return false, err
	}

	_, ignoredCommit := b.ignoreRevs[curItem.Commit.Hash]
	if ignoredCommit {
		// git only reattributes lines through parents when at least one
		// parent contains the blamed path; lines introduced by an
		// ignored revision that introduced the file stay attributed to it
		// without being flagged.
		curItem.ignoreHasParents = len(parents) > 0
	}

	anyPushed := false
	// diffParents collects the parents whose blob differs from the target;
	// the normal diff walk is run for every parent first, and ignored
	// revisions only get the fuzzy line matching afterwards for lines that
	// no parent could attribute by an exact match (mirroring git, which
	// runs the ordinary blame pass for every parent before the ignored one).
	type diffParent struct {
		parentNo   int
		commit     *object.Commit
		path       string
		contents   string
		fromParent []lineMap
		hunks      []ignoreHunk
		candidates []int
	}
	var diffParents []diffParent
	// lines the exact diff attributed to some parent (target line indexes)
	exactMatched := make(map[int]bool)

	for parnetNo, prev := range parents {
		currentHash, err := blobHash(curItem.path, curItem.Commit)
		if err != nil {
			return false, err
		}
		prevHash, err := blobHash(prev.Path, prev.Commit)
		if err != nil {
			return false, err
		}
		if currentHash == prevHash {
			if len(parents) == 1 && curItem.MergedChildren == nil && curItem.IdenticalToChild {
				// commit that has 1 parent and 1 child and is the same as both, bypass it completely
				b.q.Push(&queueItem{
					Child:            curItem.Child,
					Commit:           prev.Commit,
					path:             prev.Path,
					Contents:         curItem.Contents,
					NeedsMap:         curItem.NeedsMap, // reuse the NeedsMap as we are throwing away this item
					IdenticalToChild: true,
					ParentNo:         curItem.ParentNo,
				})
			} else {
				b.q.Push(&queueItem{
					Child:            curItem,
					Commit:           prev.Commit,
					path:             prev.Path,
					Contents:         curItem.Contents,
					NeedsMap:         append([]lineMap(nil), curItem.NeedsMap...), // create new slice and copy
					IdenticalToChild: true,
					ParentNo:         parnetNo,
				})
				curItem.numParentsNeedResolving++
			}
			anyPushed = true
			for i := range curItem.NeedsMap {
				exactMatched[curItem.NeedsMap[i].Cur] = true
			}
			continue
		}

		// get the contents of the file
		file, err := prev.Commit.File(prev.Path)
		if err != nil {
			return false, err
		}
		prevContents, err := file.Contents()
		if err != nil {
			return false, err
		}

		hunks := diff.Do(prevContents, curItem.Contents)
		prevl := -1
		curl := -1
		need := 0
		needs := curItem.NeedsMap
		dp := diffParent{parentNo: parnetNo, commit: prev.Commit, path: prev.Path, contents: prevContents}
		inHunk := false
		var hunk ignoreHunk
		closeHunk := func() {
			if inHunk {
				dp.hunks = append(dp.hunks, hunk)
				inHunk = false
			}
		}
	out:
		for h := range hunks {
			hLines := countLines(hunks[h].Text)
			for range hLines {
				switch hunks[h].Type {
				case diffmatchpatch.DiffEqual:
					closeHunk()
					prevl++
					curl++
					for need < len(needs) && curl == needs[need].Cur {
						// add to needs
						dp.fromParent = append(dp.fromParent, lineMap{
							Orig:    curl,
							Cur:     prevl,
							ignored: needs[need].ignored,
						})
						exactMatched[curl] = true
						// move to next need
						need++
						if need >= len(needs) {
							break out
						}
					}
				case diffmatchpatch.DiffInsert:
					if ignoredCommit && !inHunk {
						inHunk = true
						hunk = ignoreHunk{startA: prevl + 1, startB: curl + 1}
					}
					curl++
					if inHunk {
						hunk.countB++
					}
					for need < len(needs) && curl == needs[need].Cur {
						if ignoredCommit {
							// the line was changed or added by an ignored
							// commit; the fingerprint heuristic may still
							// find an equivalent line in the parent.
							dp.candidates = append(dp.candidates, curl)
						}
						// the line we want is added, it may have been added here (or by another parent), skip it for now
						need++
						if need >= len(needs) {
							closeHunk()
							break out
						}
					}
				case diffmatchpatch.DiffDelete:
					if ignoredCommit && !inHunk {
						inHunk = true
						hunk = ignoreHunk{startA: prevl + 1, startB: curl + 1}
					}
					if inHunk {
						hunk.countA += hLines
					}
					prevl += hLines
					continue out
				default:
					return false, errors.New("invalid state: invalid hunk Type")
				}
			}
		}
		closeHunk()

		diffParents = append(diffParents, dp)
	}

	if ignoredCommit {
		var targetLines []string
		if len(diffParents) > 0 {
			targetLines = splitLines(curItem.Contents)
		}
		for i := range diffParents {
			dp := &diffParents[i]
			candidates := dp.candidates[:0:0]
			for _, targetIdx := range dp.candidates {
				if !exactMatched[targetIdx] {
					candidates = append(candidates, targetIdx)
				}
			}
			if len(candidates) == 0 {
				continue
			}
			parentLines := splitLines(dp.contents)
			// fuzzy matches can land on parent lines that the exact diff
			// matched for other target lines too (a line moved onto a line
			// that is also kept); overlapping attributions are kept.
			for targetIdx, parentIdx := range b.guessIgnoredLineOrigins(dp.hunks, candidates, parentLines, targetLines) {
				dp.fromParent = append(dp.fromParent, lineMap{
					Orig:    targetIdx,
					Cur:     parentIdx,
					ignored: true,
				})
			}
		}
	}

	for i := range diffParents {
		dp := &diffParents[i]
		if len(dp.fromParent) == 0 {
			continue
		}
		needsMap := dp.fromParent
		var origIndex map[int]int
		if ignoredCommit {
			// fuzzy matches are not ordered by their position in the
			// parent file; sort the needs so the parent item's diff walk
			// can consume them in line order, and build an index keyed by
			// Orig so applyNeeds does not rely on ordering when feeding
			// results back.
			needsMap = append([]lineMap(nil), dp.fromParent...)
			sort.SliceStable(needsMap, func(i, j int) bool {
				return needsMap[i].Cur < needsMap[j].Cur
			})
			origIndex = make(map[int]int, len(needsMap))
			for i := range needsMap {
				origIndex[needsMap[i].Orig] = i
			}
		}
		b.q.Push(&queueItem{
			Child:            curItem,
			Commit:           dp.commit,
			path:             dp.path,
			Contents:         dp.contents,
			NeedsMap:         needsMap,
			IdenticalToChild: false,
			ParentNo:         dp.parentNo,
			OrigIndex:        origIndex,
		})
		curItem.numParentsNeedResolving++
		anyPushed = true
	}

	curItem.Contents = "" // no longer need, free the memory

	if !anyPushed {
		return b.finishNeeds(curItem)
	}

	return false, nil
}

func (b *blame) finishNeeds(curItem *queueItem) (bool, error) {
	_, ignoredCommit := b.ignoreRevs[curItem.Commit.Hash]
	// any needs left in the needsMap must have come from this revision
	for i := range curItem.NeedsMap {
		if curItem.NeedsMap[i].Commit == nil {
			curItem.NeedsMap[i].Commit = curItem.Commit
			curItem.NeedsMap[i].FromParentNo = -1
			if ignoredCommit && curItem.ignoreHasParents {
				// the line was introduced by an ignored revision and
				// could not be attributed to any of its parents
				curItem.NeedsMap[i].unblamable = true
			}
		}
	}

	if curItem.Child == nil && curItem.MergedChildren == nil {
		return true, nil
	}

	if curItem.MergedChildren == nil {
		return b.applyNeeds(curItem.Child, curItem.NeedsMap, curItem.OrigIndex, curItem.IdenticalToChild, curItem.ParentNo)
	}

	for _, ctn := range curItem.MergedChildren {
		m := 0 // position in merged needs map
		p := 0 // position in parent needs map
		for p < len(ctn.NeedsMap) && m < len(curItem.NeedsMap) {
			switch {
			case ctn.NeedsMap[p].Cur == curItem.NeedsMap[m].Cur:
				ctn.NeedsMap[p].Commit = curItem.NeedsMap[m].Commit
				// ignored is a property of the attribution to this
				// child and is already recorded on the child's entry;
				// only unblamable is an outcome of the resolved commit.
				ctn.NeedsMap[p].unblamable = ctn.NeedsMap[p].unblamable || curItem.NeedsMap[m].unblamable
				m++
				p++
			case ctn.NeedsMap[p].Cur < curItem.NeedsMap[m].Cur:
				p++
			default:
				m++
			}
		}
		finished, err := b.applyNeeds(ctn.Child, ctn.NeedsMap, ctn.OrigIndex, ctn.IdenticalToChild, ctn.ParentNo)
		if finished || err != nil {
			return finished, err
		}
	}

	return false, nil
}

func (b *blame) applyNeeds(child *queueItem, needsMap []lineMap, origIndex map[int]int, identicalToChild bool, parentNo int) (bool, error) {
	assign := func(l, src *lineMap) {
		l.Commit = src.Commit
		l.FromParentNo = parentNo
		l.ignored = src.ignored
		l.unblamable = src.unblamable
	}
	switch {
	case identicalToChild:
		for i := range child.NeedsMap {
			l := &child.NeedsMap[i]
			if l.Cur != needsMap[i].Cur || l.Orig != needsMap[i].Orig {
				return false, errors.New("needsMap isn't the same? Why not??")
			}
			if l.Commit == nil || parentNo < l.FromParentNo {
				assign(l, &needsMap[i])
			}
		}
	case origIndex != nil:
		// fuzzy matches can point back at non-contiguous target lines, look
		// entries up by their position in the child file rather than
		// relying on the order of the needs map
		for j := range child.NeedsMap {
			l := &child.NeedsMap[j]
			if i, ok := origIndex[l.Cur]; ok {
				if l.Commit == nil || parentNo < l.FromParentNo {
					assign(l, &needsMap[i])
				}
			}
		}
	default:
		i := 0
	out:
		for j := range child.NeedsMap {
			l := &child.NeedsMap[j]
			for needsMap[i].Orig < l.Cur {
				i++
				if i == len(needsMap) {
					break out
				}
			}
			if l.Cur == needsMap[i].Orig {
				if l.Commit == nil || parentNo < l.FromParentNo {
					assign(l, &needsMap[i])
				}
			}
		}
	}
	child.numParentsNeedResolving--
	if child.numParentsNeedResolving == 0 {
		finished, err := b.finishNeeds(child)
		if finished || err != nil {
			return finished, err
		}
	}

	return false, nil
}

// String prints the results of a Blame using git-blame's style.
func (b BlameResult) String() string {
	var buf bytes.Buffer

	// max line number length
	mlnl := len(strconv.Itoa(len(b.Lines)))
	// max author length
	mal := b.maxAuthorLength()
	format := fmt.Sprintf("%%s (%%-%ds %%s %%%dd) %%s\n", mal, mlnl)

	for ln := range b.Lines {
		_, _ = fmt.Fprintf(&buf, format, b.Lines[ln].Hash.String()[:8],
			b.Lines[ln].AuthorName, b.Lines[ln].Date.Format("2006-01-02 15:04:05 -0700"), ln+1, b.Lines[ln].Text)
	}
	return buf.String()
}

// utility function to calculate the number of runes needed
// to print the longest author name in the blame of a file.
func (b BlameResult) maxAuthorLength() int {
	m := 0
	for ln := range b.Lines {
		m = max(m, utf8.RuneCountInString(b.Lines[ln].AuthorName))
	}
	return m
}

type childToNeedsMap struct {
	Child            *queueItem
	NeedsMap         []lineMap
	OrigIndex        map[int]int
	IdenticalToChild bool
	ParentNo         int
}

type queueItem struct {
	Child                   *queueItem
	MergedChildren          []childToNeedsMap
	Commit                  *object.Commit
	path                    string
	Contents                string
	NeedsMap                []lineMap
	OrigIndex               map[int]int
	numParentsNeedResolving int
	IdenticalToChild        bool
	ParentNo                int
	// ignoreHasParents is set when the item is an ignored revision whose
	// file exists in at least one parent: lines that cannot be attributed
	// to a parent are unblamable in that case.
	ignoreHasParents bool
}

type priorityQueueImp []*queueItem

func (pq *priorityQueueImp) Len() int { return len(*pq) }
func (pq *priorityQueueImp) Less(i, j int) bool {
	return !(*pq)[i].Commit.Less((*pq)[j].Commit)
}
func (pq *priorityQueueImp) Swap(i, j int) { (*pq)[i], (*pq)[j] = (*pq)[j], (*pq)[i] }
func (pq *priorityQueueImp) Push(x any)    { *pq = append(*pq, x.(*queueItem)) }
func (pq *priorityQueueImp) Pop() any {
	n := len(*pq)
	ret := (*pq)[n-1]
	(*pq)[n-1] = nil // ovoid memory leak
	*pq = (*pq)[0 : n-1]

	return ret
}

func (pq *priorityQueueImp) Peek() *object.Commit {
	if len(*pq) == 0 {
		return nil
	}
	return (*pq)[0].Commit
}

type priorityQueue priorityQueueImp

func (pq *priorityQueue) Init()    { heap.Init((*priorityQueueImp)(pq)) }
func (pq *priorityQueue) Len() int { return (*priorityQueueImp)(pq).Len() }
func (pq *priorityQueue) Push(c *queueItem) {
	heap.Push((*priorityQueueImp)(pq), c)
}

func (pq *priorityQueue) Pop() *queueItem {
	return heap.Pop((*priorityQueueImp)(pq)).(*queueItem)
}
func (pq *priorityQueue) Peek() *object.Commit { return (*priorityQueueImp)(pq).Peek() }

type parentCommit struct {
	Commit *object.Commit
	Path   string
}

func parentsContainingPath(path string, c *object.Commit) ([]parentCommit, error) {
	// TODO: benchmark this method making git.object.Commit.parent public instead of using
	// an iterator
	var result []parentCommit
	iter := c.Parents()
	for {
		parent, err := iter.Next()
		if err == io.EOF {
			return result, nil
		}
		if err != nil {
			return nil, err
		}
		if _, err := parent.File(path); err == nil {
			result = append(result, parentCommit{parent, path})
		} else {
			// look for renames
			patch, err := parent.Patch(c)
			if err != nil {
				return nil, err
			} else if patch != nil {
				for _, fp := range patch.FilePatches() {
					from, to := fp.Files()
					if from != nil && to != nil && to.Path() == path {
						result = append(result, parentCommit{parent, from.Path()})
						break
					}
				}
			}
		}
	}
}

func blobHash(path string, commit *object.Commit) (plumbing.Hash, error) {
	file, err := commit.File(path)
	if err != nil {
		return plumbing.ZeroHash, err
	}
	return file.Hash, nil
}

// splitLines splits blob contents into lines, matching the line splitting
// used by the rest of the blame machinery.
func splitLines(content string) []string {
	if content == "" {
		return nil
	}
	lines := strings.Split(content, "\n")
	if lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	return lines
}

// guessIgnoredLineOrigins mirrors git's ignore-rev heuristic: for lines that
// an ignored revision changed relative to one of its parents it tries to find
// their likely origin in the parent. It returns the parent line index for
// every target line (indexed by its target line number) that can be
// attributed to the parent. Target lines that cannot be matched are left out
// and stay attributed to the ignored revision.
func (b *blame) guessIgnoredLineOrigins(hunks []ignoreHunk, candidates []int, parentLines, targetLines []string) map[int]int {
	matches := make(map[int]int)
	if len(parentLines) == 0 || len(targetLines) == 0 {
		return matches
	}
	parentFp := newLineFingerprints(parentLines)
	targetFp := newLineFingerprints(targetLines)

	isCandidate := make(map[int]bool, len(candidates))
	for _, idx := range candidates {
		isCandidate[idx] = true
	}

	for _, hk := range hunks {
		startA, lenA := hk.startA, hk.countA
		startB, lenB := hk.startB, hk.countB
		if startA >= len(parentLines) {
			startA, lenA = len(parentLines), 0
		} else if startA+lenA > len(parentLines) {
			lenA = len(parentLines) - startA
		}
		if startB >= len(targetLines) {
			startB, lenB = len(targetLines), 0
		} else if startB+lenB > len(targetLines) {
			lenB = len(targetLines) - startB
		}
		if lenB == 0 {
			continue
		}

		// First pass: look for matches near where the diff hunks place the
		// line, matching git's fuzzy within-chunk line matching.
		var fuzzy []int
		if lenA > 0 {
			fuzzy = fuzzyFindMatchingLines(parentFp, targetFp, startA, lenA, startB, lenB)
		}
		for i := range lenB {
			targetIdx := startB + i
			if !isCandidate[targetIdx] {
				continue
			}
			if fuzzy != nil && fuzzy[i] >= 0 {
				matches[targetIdx] = fuzzy[i]
				continue
			}
			// Second pass: a line unmatched within the hunk may have moved
			// elsewhere in the parent file.
			if parentIdx := scanParentRange(parentFp, targetFp, targetIdx, 0, len(parentLines)); parentIdx >= 0 {
				matches[targetIdx] = parentIdx
			}
		}
	}

	return matches
}

// fingerprintFileThreshold is the minimum similarity between two line
// fingerprints for a whole-file match, matching git's FINGERPRINT_FILE_THRESHOLD.
const fingerprintFileThreshold = 10

// scanParentRange searches every parent line for the best fingerprint match
// with target line tIdx. A match must be at least fingerprintFileThreshold
// similar; ties are broken in favour of the line closest to the target's
// position.
func scanParentRange(parentFp, targetFp []lineFingerprint, tIdx, from, nLines int) int {
	bestSim := fingerprintFileThreshold
	bestIdx := -1
	for p := from; p < from+nLines; p++ {
		sim := fingerprintSimilarity(targetFp[tIdx], parentFp[p])
		if sim < bestSim {
			continue
		}
		// break ties with the closest-to-target line number
		if sim == bestSim && bestIdx != -1 && abs(bestIdx-tIdx) < abs(p-tIdx) {
			continue
		}
		bestSim = sim
		bestIdx = p
	}
	return bestIdx
}

// Certainty values for fuzzy line matching, mirroring git's
// CERTAIN_NOTHING_MATCHES and CERTAINTY_NOT_CALCULATED.
const (
	certainNothingMatches  = -2
	certaintyNotCalculated = -1
	fuzzyMaxSearchDistance = 10
)

// fuzzyFindMatchingLines ports git's fuzzy_find_matching_lines: it finds the
// parent lines in the window [startA, startA+lenA) that most closely match
// the target lines in [startB, startB+lenB), choosing matches that preserve
// the line ordering. Returns a slice indexed by target line (relative to
// startB) holding the matched parent line index, or -1. Fingerprints use
// absolute line indexes for the whole file.
func fuzzyFindMatchingLines(parentFp, targetFp []lineFingerprint, startA, lenA, startB, lenB int) []int {
	if lenA <= 0 {
		return nil
	}
	maxA := fuzzyMaxSearchDistance
	if maxA >= lenA {
		maxA = lenA - 1
	}
	maxB := ((2*maxA+1)*lenB - 1) / lenA
	width := 2*maxA + 1

	result := make([]int, lenB)
	secondBest := make([]int, lenB)
	certainties := make([]int, lenB)
	similarities := make([]int, lenB*width)
	for i := range similarities {
		similarities[i] = -1
	}
	for i := range lenB {
		result[i] = -1
		secondBest[i] = -1
		certainties[i] = certaintyNotCalculated
	}

	// the fingerprints of parent lines are consumed as lines are matched,
	// so work on a copy of the window
	fpA := make([]lineFingerprint, lenA)
	for i := range lenA {
		fpA[i] = cloneLineFingerprint(parentFp[startA+i])
	}
	fpB := targetFp[startB : startB+lenB]

	// mapLineNumber maps a target line number onto the parent window,
	// scaling and offsetting the window ranges onto each other
	mapLineNumber := func(lineNumber int) int {
		return ((lineNumber-startB)*2+1)*lenA/(lenB*2) + startA
	}

	var recurse func(frameStartA, frameStartB, frameLenA, frameLenB int)
	recurse = func(frameStartA, frameStartB, frameLenA, frameLenB int) {
		mostCertainB := -1
		mostCertainty := -1
		for localB := range frameLenB {
			absB := frameStartB + localB
			bIdx := absB - startB
			if certainties[bIdx] != certaintyNotCalculated {
				continue
			}
			closestA := mapLineNumber(absB)
			closestLocalA := closestA - frameStartA

			searchStart := max(closestLocalA-maxA, 0)
			searchEnd := min(closestLocalA+maxA+1, frameLenA)

			bestSim, secondBestSim := 0, 0
			bestIdx, secondBestIdx := 0, 0
			for localA := searchStart; localA < searchEnd; localA++ {
				simIdx := localA - closestLocalA + maxA + bIdx*width
				if similarities[simIdx] == -1 {
					similarities[simIdx] = fingerprintSimilarity(fpB[bIdx], fpA[localA+frameStartA-startA]) *
						(1000 - abs(localA-closestLocalA))
				}
				switch {
				case similarities[simIdx] > bestSim:
					secondBestSim = bestSim
					secondBestIdx = bestIdx
					bestSim = similarities[simIdx]
					bestIdx = localA
				case similarities[simIdx] > secondBestSim:
					secondBestSim = similarities[simIdx]
					secondBestIdx = localA
				}
			}

			if bestSim == 0 {
				certainties[bIdx] = certainNothingMatches
				result[bIdx] = -1
				continue
			}
			certainties[bIdx] = bestSim*2 - secondBestSim
			result[bIdx] = frameStartA + bestIdx
			secondBest[bIdx] = frameStartA + secondBestIdx
			if certainties[bIdx] > mostCertainty {
				mostCertainty = certainties[bIdx]
				mostCertainB = localB
			}
		}

		if mostCertainB == -1 {
			return
		}
		mostAbsB := frameStartB + mostCertainB
		mostAbsA := result[mostAbsB-startB]

		// consume the matched parent line's fingerprint so other lines
		// cannot match the same parts of it
		fingerprintSubtract(fpA[mostAbsA-startA], fpB[mostAbsB-startB])

		invalidateMin := max(mostCertainB-maxB, 0)
		invalidateMax := min(mostCertainB+maxB+1, frameLenB)

		for i := invalidateMin; i < invalidateMax; i++ {
			absB := frameStartB + i
			bIdx := absB - startB
			closestLocalA := mapLineNumber(absB) - frameStartA
			if abs(mostAbsA-frameStartA-closestLocalA) > maxA {
				continue
			}
			simIdx := mostAbsA - frameStartA - closestLocalA + maxA + bIdx*width
			similarities[simIdx] = -1
		}
		for i := mostCertainB - 1; i >= invalidateMin; i-- {
			bIdx := frameStartB - startB + i
			if certainties[bIdx] >= 0 &&
				(result[bIdx] >= mostAbsA || secondBest[bIdx] >= mostAbsA) {
				certainties[bIdx] = certaintyNotCalculated
			}
		}
		for i := mostCertainB + 1; i < invalidateMax; i++ {
			bIdx := frameStartB - startB + i
			if certainties[bIdx] >= 0 &&
				(result[bIdx] <= mostAbsA || secondBest[bIdx] <= mostAbsA) {
				certainties[bIdx] = certaintyNotCalculated
			}
		}

		if mostCertainB > 0 {
			recurse(frameStartA, frameStartB, mostAbsA+1-frameStartA, mostCertainB)
		}
		if mostCertainB+1 < frameLenB {
			secondStartA := mostAbsA
			secondStartB := frameStartB + mostCertainB + 1
			secondLenA := frameLenA + frameStartA - secondStartA
			secondLenB := frameLenB + frameStartB - secondStartB
			recurse(secondStartA, secondStartB, secondLenA, secondLenB)
		}
	}

	recurse(startA, startB, lenA, lenB)
	return result
}

// lineFingerprint loosely represents a line's content: the multiset of
// lower-cased byte pairs in the line, with whitespace normalised to 0 and
// whitespace pairs ignored. The similarity between two fingerprints is the
// size of the multiset intersection. This mirrors git's struct fingerprint.
type lineFingerprint map[uint16]int

func newLineFingerprints(lines []string) []lineFingerprint {
	fp := make([]lineFingerprint, len(lines))
	for i := range lines {
		fp[i] = newLineFingerprint(lines[i])
	}
	return fp
}

func cloneLineFingerprint(fp lineFingerprint) lineFingerprint {
	clone := make(lineFingerprint, len(fp))
	maps.Copy(clone, fp)
	return clone
}

func newLineFingerprint(line string) lineFingerprint {
	fp := make(lineFingerprint)
	var c0 uint16
	for i := 0; i <= len(line); i++ {
		var c1 uint16
		switch {
		case i == len(line) || isASCIISpace(line[i]):
			c1 = 0
		default:
			c := line[i]
			if c >= 'A' && c <= 'Z' {
				c += 'a' - 'A'
			}
			c1 = uint16(c)
		}
		if pair := c0 | c1<<8; pair != 0 {
			fp[pair]++
		}
		c0 = c1
	}
	return fp
}

func isASCIISpace(c byte) bool {
	switch c {
	case ' ', '\t', '\n', '\v', '\f', '\r':
		return true
	}
	return false
}

func fingerprintSimilarity(a, b lineFingerprint) int {
	similarity := 0
	for pair, countB := range b {
		if countA, ok := a[pair]; ok {
			if countA < countB {
				similarity += countA
			} else {
				similarity += countB
			}
		}
	}
	return similarity
}

// fingerprintSubtract removes the byte pairs in b from a.
func fingerprintSubtract(a, b lineFingerprint) {
	for pair, countB := range b {
		if countA, ok := a[pair]; ok {
			if countA <= countB {
				delete(a, pair)
			} else {
				a[pair] = countA - countB
			}
		}
	}
}

func abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}
