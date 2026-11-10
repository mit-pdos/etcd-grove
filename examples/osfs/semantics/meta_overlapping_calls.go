//go:build linux

package semantics

import (
	"os"
	"sync"
)

// Overlapping metadata calls on unrelated directories (model decision).
//
// Decision: metadata calls may overlap. Two overlapping calls are unordered: a
// crash may keep either without the other (even where Linux serializes them,
// on a common directory's lock or the rename lock: more crashes than Linux
// has, which is sound).
//
// Lean: Impl.lean: CallBegin (the token records the log's length when the
// call began, LogEntry.start); Tree.lean: Follows (only the start order);
// Tests.lean: crash_overlap.
//
// Allowed: after the crash below, any of {}, {x/a}, {y/b}, {x/a, y/b}, even if
// the model logged a first.
// Excluded: none of these.
//
// Why: either order is a possible journal order (they take no common lock, so
// they may join transactions in either order), and an observer cannot rely on
// one (axiom review round 1, finding 4). Needed for etcd: its WAL file
// pipeline creates the next segment while `cut` renames, and purge removes
// old segments beside both.
func OverlappingCalls(dir string) {
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { f, _ := os.Create(dir + "/x/a"); f.Close(); wg.Done() }()
	go func() { f, _ := os.Create(dir + "/y/b"); f.Close(); wg.Done() }()
	wg.Wait()
	// crash here
	// allowed: {}, {x/a}, {y/b}, {x/a, y/b}
}

// Two overlapping calls on the same directory are ordered by its lock
// (i_rwsem): a crash that keeps the later keeps the earlier.
func OverlappingSameDir(dir string) {
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { f, _ := os.Create(dir + "/x/a"); f.Close(); wg.Done() }()
	go func() { f, _ := os.Create(dir + "/x/b"); f.Close(); wg.Done() }()
	wg.Wait()
	// crash here
	// allowed:  a prefix of the order the model logged them in
	// excluded: the second logged without the first
}
