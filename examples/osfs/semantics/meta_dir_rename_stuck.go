//go:build linux

package semantics

import (
	"os"
	"sync"
)

// A rename of a directory is stuck while another path call in its root's tree
// is in flight (model decision; scoped 2026-11-17, approved by the user, WAL
// link L4, notes/wal-link-l4-fsext.md).
//
// Decision: every call on a path begins with CallBegin of that path (one per
// system-call attempt) and the model resolves the path at the call's step, in
// one tree. A rename whose source is a directory is stuck while another such
// call on a path in the source's root's tree is in flight (the target is in
// the same root: meta_rename_cross_root.go). A proved program therefore never
// overlaps a directory rename with another path call in that root's tree.
//
// Lean: Impl.lean: the CallBegin step (`v = #p`), ProcState.calls (the log's
// length and the path), OsState.SameRoot, the Rename step's clause
// `(∃ j, st.lookup s = some (.dir j)) → ∀ k' start' p', … → k' = k ∨ ¬ st.SameRoot s p'`;
// notes/axiom-review/fs-v2-r2.md, notes/wal-link-l4-fsext.md.
//
// Excluded (stuck): the overlap below, within one root's tree.
// Allowed: a directory rename in root A while a call on a path in root B (or
// above the roots) is in flight.
//
// Why: documented (Documentation/filesystems/path-lookup.rst): Linux walks a
// path a component at a time, validating only each parent's d_seq as it
// steps. A walk of a/b/c racing `rename(a/b, x/b)` can resolve a path no
// single tree of the log has (a/b found before the move, c looked up after
// it). A rename off the walk's path changes only timing (rename_lock retries
// in d_lookup/d_alloc_parallel, waits on s_vfs_rename_mutex), never the
// result; and a walk of a path in another root's tree, or above the roots,
// never passes through this root's tree (roots are not nested, and no root's
// ancestor resolves into another root's tree). Measured:
// meta_rename_scoped_test.go, TestDirRenameScopedToRoot (no deviation on
// this machine's ext4; the configuration-C run is an open obligation of the
// note). Needed for etcd: the k members of one process each have their WAL
// under their own root, and member j's wal.Create renames its directory while
// member j-1's WAL appends and cuts.
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
