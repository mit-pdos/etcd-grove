//go:build linux

package semantics

import (
	"os"
)

// Files have identity (inodes), hidden from the API (model decision).
//
// Decision: files and directories are keyed by internal inode numbers,
// allocated at create; no call takes or returns one. Fds, mappings and
// in-flight changes hold the inode, so they follow a file across rename and
// survive unlink; a crash drops every inode the surviving tree does not name.
//
// Lean: Tree.lean: Ino, Node, Tree, MetaOp (by directory inode and name);
// Impl.lean: FsState.files, FsState.nextIno, OsFd.ino, Named, MachineCrash
// (unnamed inodes dropped); Tests.lean: crash_old_name_new_bytes;
// notes/fs-semantics-v2.md, V2.
//
// Allowed: after the crash below, `a.tmp` holding Y: the rename was not
// committed, but the write after it went to the same inode and was written
// back.
// Excluded: nothing here; a model keyed by path alone would exclude this
// outcome (unsound) or have to rebuild identity elsewhere.
//
// Why: Linux's fds, page cache and writeback are per inode; a rename moves a
// name, not data. etcd relies on identity: wal.cut renames the open tail
// segment (its fd keeps working), and the purge loop removes a segment another
// fd still has locked.
func InodesHidden(dir string) {
	f, _ := os.Create(dir + "/a.tmp")
	f.WriteAt([]byte("X"), 0)
	f.Sync()
	os.Rename(dir+"/a.tmp", dir+"/a")
	f.WriteAt([]byte("Y"), 0) // the same file, now named a; not synced
	// crash here
	// allowed:  a.tmp = X or Y (the rename lost; writeback may have taken Y);
	//           a = X or Y (the rename kept)
	// excluded: both names; neither name
}

// Unlinking a file an fd holds open: the fd keeps the file.
func UnlinkOpen(dir string) {
	f, _ := os.Create(dir + "/seg")
	os.Remove(dir + "/seg")
	f.WriteAt([]byte("still works"), 0) // fine: the fd holds the inode
	// crash here: the inode is not named, so it is gone
}
