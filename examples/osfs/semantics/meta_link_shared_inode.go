//go:build linux

package semantics

import (
	"os"
)

// A crash between link(2) and the removal of the temporary name can leave
// both names, one inode (an assumption of a trust-boundary axiom, not of the
// semantics: the file extension has no link and its inodes are internal,
// meta_inodes_hidden.go; 2026-11-28, review
// /shared/tmp/trust-review/row2.md, assumption (iii)).
//
// Decision: after os.Link(tmp, fn) and before os.Remove(tmp) is durable, a
// crash may keep the link and not the removal: tmp and fn then name one
// inode (link count 2) holding the synced bytes. The removal is never kept
// without the link (it began after the link returned: journal order). Once
// the directory fsync after the removal returned, only fn.
//
// Lean (branch etcd-safe-crash-delta-now/2026-11-27, head 1ecd4cc7c2): the
// tmp* names of the snapshot directory are snap.snapDirOwn's
// (Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean: the claim
// on every name of the directory but db and the canonical .snap.db ones),
// held for good by the invariant snapDirInvK/snapDirInvH
// (Proof/.../api/rafthttp/Net.lean); it claims no inode, so a tmp* name
// sharing fn's inode takes nothing from fn's backend.fileAtPend/fileAtDur.
// The axiom snap.Snapshotter.SaveDBFrom.wp_proof treats the temporary file
// as the body's scratch under that claim. The crash law
// (snapDir_crash_law_holds, Proof/.../etcdserver/SnapDirCrash.lean) says
// nothing of tmp* names.
//
// Allowed: after the first crash below: {}, {tmp}, {tmp, fn} (one inode,
// nlink 2, the stream), {fn} (the stream, nlink 1). After the second: {fn}.
// Excluded: tmp and fn as two inodes; fn with a link count of 1 while tmp
// is there; after the directory fsync, tmp.
//
// Why: kernel source (Linux v7.0, fs/ext4/namei.c): __ext4_link adds the
// entry and raises the count in one handle; __ext4_unlink removes the entry
// and drop_nlink's the count in another (adding the inode to the orphan
// list only at count 0). The two are separate jbd2 transactions, in journal
// order (fs-v2-r5.md, B1, for create/rename/unlink), so a crash can keep
// the first and not the second, and never the second alone. Measured live
// (meta_link_test.go, TestLinkSharedInode: after the link one inode, nlink 2
// for both names; after the removal nlink 1, the bytes kept; PASS on C
// through run-models-on-c.sh, fk-lean2, Linux 7.0.0-1017-aws, 2026-11-28).
// The crash states, measured on C (notes/axiom-review/fs-link/results.md:
// link.sh snapsave, five runs, 134 crash points, 0 violations): {}, {tmp},
// {tmp, fn} as one inode with nlink 2 and the stream (after the link's
// commit, before the unlink's, in the four runs where they committed
// separately), {fn} with nlink 1; never two inodes, never the removal
// without the link, never tmp after the directory fsync.
//
// Needed for etcd: SaveDBFrom (db.go:39-98, fork 30df685e4) removes the
// temporary name after the link, without a sync between them; a restart
// after such a crash finds a tmp* file beside the .snap.db. Nothing in etcd
// opens tmp* files of the snap directory (ReleaseSnapDBs and the snapshot
// lookup parse only <hex>.snap.db names), and removing tmp later leaves fn
// intact (the inode lives while a name does).
func LinkSharedInode(dir string) {
	f, _ := os.CreateTemp(dir, "tmp")
	f.Write([]byte("the snapshot stream"))
	f.Sync()
	f.Close()
	os.Link(f.Name(), dir+"/0000000000000005.snap.db")
	os.Remove(f.Name())
	// crash here
	// allowed:  {}, {tmp}, {tmp, fn} as one inode, {fn}
	// excluded: tmp and fn as different inodes
	d, _ := os.Open(dir)
	d.Sync()
	d.Close()
	// crash here
	// allowed:  {fn}
}
