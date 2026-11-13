//go:build linux

package semantics

import (
	"os"
)

// os.RemoveAll as Go's removeall_at.go body over paths (trusted model; a draft
// pending review, 2026-11-13).
//
// Decision: Go's RemoveAll (removeall_at.go) names entries under open
// directory fds (unlinkat, openat); the extension's steps name paths. The
// model is Go's body with each entry named by its path: Remove(path) first
// (unlink, then rmdir), ENOENT being success; then the parent opened; then
// removeAllFrom: unlink the entry; on EISDIR, EPERM or EACCES, passes of
// "open the directory, read all its names, remove each (recursively), close"
// (the number of passes arbitrary: Go makes another exactly when a 1024-name
// chunk was full), then rmdir; Go's errors (*PathError, with the paths
// prefixed as Go does). A CallBegin taken at the start and ended at the return
// (by a LstatDir without effect) makes every directory rename by another
// thread stuck while RemoveAll runs, so that a path names what the fd-relative
// name would.
//
// Lean: LinuxFs/TrustedCode/os.lean: RemoveAll.impl, model.removeAllFrom,
// model.unlinkLoop, model.rmdirLoop, model.openLoop, model.pathErrorPtr,
// model.prefixPath; the translated splitPath and endsWithDot; Impl.lean:
// CallBegin, LstatDir, Rename (the stuck clause: meta_dir_rename_stuck.go).
//
// Allowed: below, after RemoveAll returns nil, d and everything under it
// gone; after a crash, any prefix of the unlinks and rmdirs in the journal's
// order (children before their directory); an error at any point, with what
// was removed so far removed. Any errno is ENOENT too, so a RemoveAll may
// return nil having removed nothing (the extension's failures are any errno):
// a proof cannot conclude more from a nil.
// Excluded: d removed while a child of it is not; a rename of a directory by
// another thread during the call (stuck: never in a proved program).
//
// Why: documented (go1.27.3 src/os/removeall_at.go, removeAll and
// removeAllFrom; src/os/root_unix.go, rootOpenDir, removefileat, removedirat).
// The fd-relative and path names agree while no directory above the entry is
// moved, which the CallBegin guarantees; a directory above it removed and
// remade by another thread is left: Go's calls then act on the removed one,
// which no path names, and the model's may fail with no effect, the outcome
// Linux leaves visible. etcd's wal.Create removes a stale dir.tmp with
// RemoveAll (and defers another), and its renameWAL removes the WAL
// directory before renaming dir.tmp to it.
func RemoveAllTree(dir string) {
	os.MkdirAll(dir+"/d/e", 0o755)
	f, _ := os.Create(dir + "/d/e/f")
	f.Close()
	os.RemoveAll(dir + "/d")
	// allowed: nil with d gone; an error with d, d/e or d/e/f still there
}
