//go:build linux

package semantics

import (
	"os"
	"sync"
)

// A rename of a directory is stuck while any other path call is in flight
// (model decision).
//
// Decision: every call on a path begins with CallBegin (one per system-call
// attempt) and the model resolves the path at the call's step, in one tree.
// A rename whose source is a directory is stuck while any other such call is
// in flight. A proved program therefore never overlaps a directory rename
// with another path call.
//
// Lean: Impl.lean: the CallBegin step, ProcState.calls, the Rename step's
// clause `(∃ j, st.lookup s = some (.dir j)) → ∀ k' start', … → k' = k`;
// notes/axiom-review/fs-v2-r2.md.
//
// Excluded (stuck): the overlap below.
//
// Why: documented (Documentation/filesystems/path-lookup.rst): Linux walks a
// path a component at a time without locking the directories it has passed.
// A walk of a/b/c racing `rename(a/b, x/b)` can resolve a path no single tree
// of the log has (a/b found before the move, c looked up after it). Resolving
// at one instant is right only when no directory moves during the walk. The
// clients rename directories only when nothing else runs (wal.Create, before
// the WAL is used), so stuck costs nothing; modelling the walk would.
func DirRenameStuck(dir string) {
	os.MkdirAll(dir+"/a/b", 0o755)
	os.Mkdir(dir+"/x", 0o755)
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		f, _ := os.Create(dir + "/a/b/c") // a path call in flight...
		f.Close()
		wg.Done()
	}()
	os.Rename(dir+"/a/b", dir+"/x/b") // ...stuck in the model while it is
	wg.Wait()
}
