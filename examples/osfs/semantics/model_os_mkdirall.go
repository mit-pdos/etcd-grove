//go:build linux

package semantics

import (
	"os"
)

// os.MkdirAll is Go's body over the models of Stat, Mkdir and Lstat (trusted
// model; a draft pending review, 2026-11-13).
//
// Decision: MkdirAll(path, perm) is Go's path.go body (the fast-path Stat, the
// recursion on the parent, Mkdir, the Lstat after a failed Mkdir), calling the
// models of Stat, Lstat and Mkdir and the translated IsPathSeparator, with
// len(filepathlite.VolumeName(path)) written as 0 (its value on Linux:
// internal/filepathlite, which nothing translates, is why MkdirAll is a model
// and not a translation).
//
// Lean: LinuxFs/TrustedCode/os.lean: MkdirAll.impl, model.stat, Mkdir.impl.
//
// Allowed: below, a, a/b and a/b/c made in that order, each Mkdir an entry of
// the log after the previous one; an error at any step stops the rest (any
// errno from Stat, Mkdir or Lstat). A Mkdir that fails because another thread
// made the directory first returns nil after the Lstat sees a directory.
// Excluded: a/b/c made before a/b.
//
// Why: documented (go1.27.3 src/os/path.go, MkdirAll; src/internal/
// filepathlite/path_unix.go, volumeNameLen returns 0). etcd's
// fileutil.TouchDirAll calls MkdirAll (then fsyncs the parents of the
// directories it made).
func MkdirAllOrder(dir string) {
	os.MkdirAll(dir+"/a/b/c", 0o700)
	// allowed after a crash: a; a/b; a/b/c; none (until the parents' fsyncs)
}
