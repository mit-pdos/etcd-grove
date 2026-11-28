//go:build linux

package semantics

import (
	"os"
)

// A crash after link(2) and before the directory's fsync leaves the new name
// absent, or present as the source's inode with its synced bytes (an
// assumption of a trust-boundary axiom, not of the semantics: the file
// extension has no link; 2026-11-28, review
// /shared/tmp/trust-review/row2.md, assumption (ii)).
//
// Decision: link joins the journal order as a create does
// (env_journal_order.go): one call, one change, kept or not by a crash, kept
// with every call that returned before it began. A kept link names the
// inode it linked, with that inode's link count raised in the same change;
// that inode's bytes and size, synced by fsync before the link began, are
// the ones the name shows. After the directory fsync that follows, the name
// is durable.
//
// Lean (branch etcd-safe-crash-delta-now/2026-11-27, head 1ecd4cc7c2): the
// axiom snap.Snapshotter.SaveDBFrom.wp_proof's ghost step at os.Link puts
// the index's file in M as backend.fileAtPend (Proof/go_etcd_io/etcd/server/
// v3/storage/backend/FileDur.lean: its bytes durable, its name
// backend.pendNamed: "nothing or the file", v = none ∨ v = some (.file i));
// at the directory sync the index joins E and the file is backend.fileAtDur
// (durNamed); snapFileAt and snapDirBody (Proof/.../api/rafthttp/Net.lean)
// state "saved means durable", and the proved crash law
// snapDir_crash_law_holds (Proof/.../etcdserver/SnapDirCrash.lean) keeps a
// pending file when the crashed tree names it and frees the name when not.
//
// Allowed: after a crash between the link and the directory fsync, no
// <index>.snap.db, or <index>.snap.db holding the whole synced stream.
// After the fsync returned: <index>.snap.db with the stream.
// Excluded: <index>.snap.db with a prefix of the stream, other bytes, size 0,
// or a link count that disagrees with its names; the name without a link
// whose call had returned before the fsync began.
//
// Why: kernel source (Linux v7.0, fs/ext4/namei.c): __ext4_link runs in one
// journal handle (ext4_journal_start(dir, EXT4_HT_DIR, ...)): ext4_inc_count
// of the inode, ext4_add_entry of the name, ext4_mark_inode_dirty, then
// d_instantiate (the name visible) and ext4_journal_stop; so the entry and
// the count are in one jbd2 transaction, committed whole or not at all, no
// earlier than the transactions of the calls that returned before it (the
// journal order, measured on C for create/rename/unlink: fs-v2-r5.md, B1).
// The inode's data blocks and size were committed by the fsync of the
// temporary file, which returned before the link began (ext4_sync_file
// waits for the data and commits the inode's transaction), so a crash that
// keeps the link's transaction keeps them. An fsync of the directory commits
// the whole journal (ext4_force_commit, as in env_journal_order.go).
// Measurement on C: notes/axiom-review/fs-link/link.sh, scenario snapsave
// (SaveDBFrom's exact calls under dm-log-writes, every flush/FUA point
// replayed, recovered by a kernel mount and checked by lreplay.py): NOT YET
// RUN, as of 2026-11-28 the machine at hand has no loop device and no
// device-mapper; until it runs, the evidence is the kernel source and
// round 5's measurement of the same journal order for rename (its `replace`
// and `segdir` scenarios: a name made after a synced file never showed a
// partial file in 54 crash points).
//
// Needed for etcd: SaveDBFrom (db.go:39-98, fork 30df685e4) creates a
// temporary file, copies the stream, fsyncs it, links it to <index>.snap.db,
// removes the temporary name and fsyncs the directory; only then does the
// receiver hand the snapshot message to raft, whose WAL record names the
// index. A crash before the directory fsync must not leave a .snap.db that a
// restart would open as a database with partial contents.
func LinkCrash(dir string) {
	fn := dir + "/0000000000000005.snap.db"
	f, _ := os.CreateTemp(dir, "tmp")
	f.Write([]byte("the snapshot stream"))
	f.Sync() // bytes and size durable
	f.Close()
	os.Link(f.Name(), fn)
	// crash here
	// allowed:  no fn; fn = "the snapshot stream"
	// excluded: fn with fewer bytes, or other bytes
	os.Remove(f.Name())
	d, _ := os.Open(dir)
	d.Sync()
	d.Close()
	// crash here
	// allowed:  fn = "the snapshot stream"
	// excluded: no fn
}
