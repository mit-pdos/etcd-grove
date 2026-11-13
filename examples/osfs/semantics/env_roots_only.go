//go:build linux

package semantics

import (
	"os"
)

// Only paths in the roots' trees are given a meaning (environment assumption).
//
// Decision: the roots (FsState.roots) are directories fixed at boot, on one
// local ext4 filesystem of configuration C (env_config.go; one journal), holding only regular files and
// directories (no symlinks, mount points, devices, hard links); no other
// process changes them. The roots and their ancestors are existing
// directories throughout (an ancestor may be a symlink to one; a root is not a
// symlink), which no other process moves and no step of the program can
// remove or rename. A call on any other path, or a path that is not canonical
// in a root's tree, is stuck: no proof can make it; the one exception is the
// query PathKind, which answers at a root and at an ancestor of one
// (model_os_mkdirall_above.go). Non-canonical paths stay stuck in every model
// (os.RemoveAll("<d>/f/"), which Linux resolves to <d>/f; os.Stat("<d>//a")):
// callers pass clean absolute paths.
//
// Lean: Impl.lean: OsState.TreeName, OsState.TreePath, OsState.AtOrAboveRoot,
// PathKind, CanonBelow (Paths.lean),
// RootsOk (Tree.lean); the header's Environment paragraph.
//
// Why: a model of one journal is only sound for one journal: two filesystems
// commit independently, so JournalOrder would be false across them. A symlink
// or mount point would make a path resolve outside the tree the model walks.
// Stuck (not an error) keeps the model no more defined than Linux.
func OutsideRoots(root string) {
	os.Create("/tmp/elsewhere")   // stuck in the model: not under a root
	os.Create(root + "/./a")      // stuck: not canonical
	os.Create(root + "/sub/../a") // stuck: not canonical
	os.Create(root + "/sub/a")    // fine
}
