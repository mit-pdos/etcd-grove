//go:build linux

package semantics

import (
	"errors"
	"os"
)

// link(2) never replaces an existing name: EEXIST, decided atomically with
// the creation of the name (an assumption of a trust-boundary axiom, not of
// the semantics: the file extension has no link; 2026-11-28, for the
// etcd_safe lead, review /shared/tmp/trust-review/row2.md, assumption (i)).
//
// Decision: os.Link(old, new) onto a name that exists fails with
// os.ErrExist and changes nothing: the existing file keeps its inode, link
// count and bytes. Of two concurrent links to one free name, exactly one
// succeeds and the name is its source's inode; the other gets EEXIST. There is
// no window between the check and the creation in which a second link (or a
// create) can put a file the first then replaces.
//
// Lean (branch etcd-safe-crash-delta-now/2026-11-27, head 1ecd4cc7c2): the
// axiom snap.Snapshotter.SaveDBFrom.wp_proof
// (Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__SaveDBFrom.lean;
// its spec's header, "The keep is atomic"): at the link of an index not yet
// in the directory, the ghost step takes the index's free name
// (backend.fileFreeDur, an F entry of snapDirBody) and puts back the file
// (snapFileAt, pending); at ErrExist "nothing" (a kept file, in M or in E\M).
// The invariant snapDirInvH / snapDirBody (Proof/.../api/rafthttp/Net.lean)
// holds one exclusive claim per name, which a link that replaced a file of M
// would contradict. The semantics (GooseLang/Ext/Fs) has no Link step.
//
// Allowed: link succeeds onto a free name; link fails with EEXIST onto a
// taken name, the taken file unchanged.
// Excluded: a link that replaces an existing file (as rename(2) does: the
// reason upstream's Exist-then-Rename was unsafe, nonissues/
// etcd-snap-savedbfrom-concurrent-rename.md); two concurrent links to one
// name both succeeding.
//
// Why: documented and measured. POSIX link(): "If the link named by the new
// argument exists, link() shall fail" with [EEXIST]; link(2): "EEXIST newpath
// already exists ... newpath will not be overwritten". Kernel source (Linux
// v7.0): linkat's filename_linkat takes the new name's parent i_rwsem
// (filename_create → __start_dirop: inode_lock_nested(dir, I_MUTEX_PARENT)
// with LOOKUP_CREATE|LOOKUP_EXCL) and holds it through vfs_link, which fails
// with -EEXIST in may_create_dentry when the dentry is positive; ext4's own
// ext4_add_entry also refuses a matching entry (ext4_find_dest_de: -EEXIST).
// The check and the creation are thus under one lock: a concurrent link,
// create or rename of the same name serialises on it. Filesystem-independent
// (VFS), so C (ext4) adds nothing. Measured: meta_link_test.go,
// TestLinkNeverReplaces (EEXIST, the existing inode, nlink 1 and bytes
// unchanged) and TestLinkRaceOneWins (5000 rounds of two goroutines linking
// their own files to one name: exactly one success every round, the name the
// winner's inode, the other ErrExist), run 2026-11-28 on this machine's ext4
// (Linux 7.0.0-1014-aws, data=ordered, delalloc, dioread_nolock, barrier),
// whose configuration check.sh could not confirm (no device node for its
// dumpe2fs, no loop device for mkfs-mount.sh); the run on C through
// run-models-on-c.sh is open.
//
// Needed for etcd: snap.SaveDBFrom (server/etcdserver/api/snap/db.go:39-98,
// fork 30df685e4) links its synced temporary file to <index>.snap.db and
// treats ErrExist as "a save of this index is already there, keep it", so
// two concurrent saves of one index (two snapshot messages from different
// leaders) never replace a file the invariant holds.
func LinkNoReplace(dir string) {
	fn := dir + "/0000000000000005.snap.db"
	os.WriteFile(fn, []byte("old"), 0o600) // a save of index 5, already there
	os.WriteFile(dir+"/tmp1", []byte("new"), 0o600)
	err := os.Link(dir+"/tmp1", fn)
	_ = errors.Is(err, os.ErrExist) // always true here
	// allowed:  fn = "old", same inode, nlink 1
	// excluded: fn = "new"
}
