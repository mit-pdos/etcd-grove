//go:build linux

package semantics

import (
	"os"
)

// os.MkdirAll at a root or above one: Go's body with no extension step, its
// Stat, Mkdir and Lstat answered as on an existing directory (trusted
// semantics and model; pending the user's review, 2026-11-13,
// notes/wal-fsext-models-review.md, finding 1).
//
// Decision: the extension's query PathKind(p) (no system call, no state
// change) is 1 for a path strictly below a root (TreeName), 0 for a root or an
// ancestor of one (AtOrAboveRoot), and stuck on any other path. MkdirAll asks
// it first; at 0 it runs Go's body without any extension step: Stat succeeds
// (nil returned) or fails with any errno; then the recursion on the parent
// (again a root's ancestor, or empty: no recursion); then Mkdir fails (the
// path exists) and Lstat sees a directory (nil returned) or fails (Mkdir's
// &PathError{"mkdir", path, Errno(e)} returned, e any nonzero errno: EEXIST on
// Linux). The environment says the roots and their ancestors are existing
// directories throughout, a root no symlink (an ancestor may be one: its
// Lstat then sees no directory, the error outcome).
//
// Lean: GooseLang/Ext/Fs/Impl.lean: PathKind, OsState.AtOrAboveRoot, the
// header's Environment ("the roots and their ancestors are existing
// directories throughout"); LinuxFs/TrustedCode/os.lean: MkdirAll.impl,
// model.mkdirAllAbove, model.mkdirAllParent.
//
// Allowed: MkdirAll(root) and MkdirAll(ancestor) return nil, or an error
// &PathError{"mkdir", q, e} with q the path or one of its ancestors; the trees
// unchanged. Excluded: any change to the trees, and nil from MkdirAll of a path
// that is neither (a path outside the roots' trees, or "", is stuck).
//
// Why: Go's MkdirAll(r + "/wal") recurses on r, and on r's parent, after Stat
// failures (each Stat may fail with any errno in the model, the extension's
// environmental failure), so before this its model was stuck on an ancestor
// of r from every call and MkdirAll had no proof (the review's finding 1).
// Measured (models_test.go, TestMkdirAllAboveRoot): Stat of an existing
// directory and of its parent succeed with a directory; Mkdir of either fails
// with EEXIST and changes nothing (the directory's inode and entries are as
// before); MkdirAll of either returns nil. Documented: go1.27.3
// src/os/path.go (MkdirAll); mkdir(2) (EEXIST: "pathname already exists").
// etcd's fileutil.TouchDirAll (the WAL's Create) calls MkdirAll(dir) on a
// directory strictly below the root.
func MkdirAllAboveRoot(root string) {
	os.MkdirAll(root, 0o700)           // nil, or a "mkdir" error; no change
	os.MkdirAll(root+"/wal", 0o700)    // may recurse on root and its ancestors
	os.MkdirAll("/elsewhere/x", 0o700) // stuck: outside the roots' trees and not above one
}
