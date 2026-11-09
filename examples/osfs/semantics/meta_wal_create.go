//go:build linux

package semantics

import (
	"os"
)

// wal.Create: a directory made to appear atomically, by journal order (model
// decision, a consequence of env_journal_order.go and meta_dir_fds.go).
//
// Decision: the fsync of the parent after `rename(dir.tmp, dir)` makes the
// rename durable with everything it follows, including the create of the
// first segment inside dir.tmp, whose directory was never synced. The
// directory fsync of a directory made in this run commits (no rule about
// paths rebound since the log's start).
//
// Lean: Impl.lean: DirSync (commitThrough (lastTouch …)); Tree.lean: Follows
// (the create returned before the rename began), Needed; Tests.lean:
// dirsync_new_dir; the walfs example's DirSwap (examples/osfs/walfs/dirswap.go)
// and its proof.
//
// Allowed: after the crash below (after Create returns), dir/seg with the
// data.
// Excluded: dir without seg.
//
// Why: etcd's wal.Create (server/storage/wal/wal.go) does exactly this:
// CreateDirAll(dirpath.tmp), the first segment created, preallocated and
// synced in it, Rename(tmp, dirpath), then Fsync of the parent; it never
// syncs the temporary directory. Under POSIX (each directory's entries
// durable only through its own fsync) a crash could keep the rename and lose
// seg's entry; under the journal's order (assumed, env_journal_order.go) the
// rename's commit carries the create before it. The first version of the
// model committed nothing for a directory made since the log's start, which
// made this unprovable; directories as inodes removed that rule.
func WalCreate(dir string) {
	tmp := dir + "/wal.tmp"
	os.Mkdir(tmp, 0o750)
	f, _ := os.OpenFile(tmp+"/seg", os.O_RDWR|os.O_CREATE, 0o666)
	f.WriteAt([]byte("record"), 0)
	f.Sync() // data and size; no name (meta_file_fsync.go)
	f.Close()
	os.Rename(tmp, dir+"/wal")
	p, _ := os.Open(dir)
	p.Sync() // the rename, and the mkdir and create it follows
	p.Close()
	// crash here
	// allowed:  wal/seg = "record"
	// excluded: wal/ without seg; wal.tmp/ remaining
}
