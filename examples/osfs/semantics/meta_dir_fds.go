//go:build linux

package semantics

import (
	"os"
)

// Directory fds hold the directory's inode; rename and rmdir with one open are
// allowed (model decision).
//
// Decision: a directory fd refers to the directory by inode. Renaming the
// directory, or a directory above it, keeps the fd on it; removing it leaves
// an empty, unreachable directory the fd still reads (no names) and syncs. A
// directory fsync makes every logged change durable.
//
// Lean: Impl.lean: OsDirFd (ino), DirSync (commitAll), DirReadNext ("A
// removed directory has no names"); Tree.lean: TreeWf (removed directories
// allowed); Tests.lean: rmdir_open_fd;
// notes/fs-semantics-v2.md, "Directories as inodes".
//
// Allowed: the fsync below commits the create of wal2/seg, under the
// directory's new name.
// Excluded: nothing; the first version of the model had these calls stuck.
//
// Why: Linux's open directory refers to the dentry/inode, not a path. etcd
// keeps its WAL directory open for the WAL's whole life (wal.dirFile, synced
// after each cut's rename), and wal.Create renames the directory it made.
func DirFds(dir string) {
	os.Mkdir(dir+"/wal", 0o755)
	d, _ := os.Open(dir + "/wal")
	os.Rename(dir+"/wal", dir+"/wal2") // d still refers to the directory
	f, _ := os.Create(dir + "/wal2/seg")
	f.Close()
	d.Sync() // commits seg's create (and the rename, which it follows)
	// crash here
	// allowed: wal2/seg exists
	// excluded: wal/ without the rename, or wal2/ without seg
}

// Rmdir with an fd open on the directory.
func RmdirOpen(dir string) {
	os.Mkdir(dir+"/t", 0o755)
	d, _ := os.Open(dir + "/t")
	os.Remove(dir + "/t")
	names, _ := d.Readdirnames(-1) // no names
	_ = names
	d.Close()
}
