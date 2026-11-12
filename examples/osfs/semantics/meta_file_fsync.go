//go:build linux

package semantics

import (
	"os"
)

// A file fsync commits no name (model decision).
//
// Decision: fsync and fdatasync of a regular file make its data and size
// durable and commit no metadata operation; only a directory fsync commits
// names (meta_dir_fds.go). fdatasync is treated as fsync.
//
// Lean: Impl.lean: the Fsync step (OsFile.synced only, metaLog untouched),
// DirSync.
//
// Allowed: after the crash below, no file named f, though its fsync returned.
// Excluded: f with lost data once its name is durable.
//
// Why: weaker than Linux, so sound: ext4 commits the running transaction on a
// file fsync (and ext4_sync_parent for a new inode), which usually commits
// the create too; POSIX promises nothing for the name. Programs must fsync the directory,
// as etcd's fileutil and bbolt do. fdatasync = fsync is sound for the size:
// ext4 sets i_datasync_tid whenever i_disksize changes, so fdatasync persists
// a size change (the audit's "Attacks the model survived").
func FileFsyncNoName(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt([]byte("data"), 0)
	f.Sync()
	// crash here
	// allowed: no f; f = "data"
	// the model never gives: f empty (its size and data were synced)
}
