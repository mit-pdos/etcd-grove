// Package restarteagerfold is the Go evidence for notes/axiom-review/bootstrap-crash-eagerfold.md:
// bootstrap's restart contract (bootstrapRestartContract, InvRestart.lean; its crash form
// bootstrapCrashContract, InvCrashImage.lean) equates, in its post (wal.restartOk's walOpened/walOpenedH,
// through walRecs), the EAGER fold of the WAL's history (every snapshot record applied,
// walFoldChkFrom walFresh) with the records sigma its pre reads (walFiles' walRead: the snapshot records
// above the last saved commit dropped, walKeep). The two differ on a WAL that ends with a synced snapshot
// record above the last saved commit, and wal.Open + ReadAll read such a WAL without error. At the etcd
// pin 30df685e4 (examples/go.mod).
//
// How etcd gets there: a follower receives MsgSnap at an index S above its saved commit; raftNode calls
// SaveSnap first (raft.go:266-271), which ends in w.sync() (wal.go:1423); a crash or kill before the
// following Save(hs{commit=S}) leaves the synced record. The test writes the same records through the
// WAL's API and closes it (Close adds no record and syncs, so the files are also a graceful image's,
// srvFiles' with the synced mark at the whole history).
//
// What it shows (TestTrailingSnapAboveCommit): after Save(commit 5, entries 1..5), SaveSnapshot(3),
// SaveSnapshot(10), Close:
//   - ValidSnapshotEntries keeps only the records at or below the commit: the newest is 3
//     (wal.go:974), as walRead's walKeep;
//   - Open(3) + ReadAll returns err = nil, commit 5, entries [4 5]: the real records have base 3;
//   - the eager fold of the same history applies the record at 10 (base 10, no entries), so no sigma
//     is both walRead's (the pre) and the eager fold's (the post), while bootstrap's WAL read succeeds.
//
// Run: cd examples && go test ./axiomcx/restarteagerfold/ -v
package restarteagerfold

import (
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
)

func u(x uint64) *uint64 { return &x }

func TestTrailingSnapAboveCommit(t *testing.T) {
	wd := t.TempDir() + "/wal"
	lg := zap.NewNop()
	w, err := wal.Create(lg, wd, []byte("md"))
	if err != nil {
		t.Fatal(err)
	}
	var ents []*raftpb.Entry
	for i := uint64(1); i <= 5; i++ {
		ents = append(ents, &raftpb.Entry{Index: u(i), Term: u(1)})
	}
	if err := w.Save(&raftpb.HardState{Term: u(1), Commit: u(5)}, ents); err != nil {
		t.Fatal(err)
	}
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: u(3), Term: u(1), ConfState: &raftpb.ConfState{}}); err != nil {
		t.Fatal(err)
	}
	// a received snapshot above the commit: SaveSnapshot returns synced; no Save(hs{commit=10}) follows
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: u(10), Term: u(1), ConfState: &raftpb.ConfState{}}); err != nil {
		t.Fatal(err)
	}
	if err := w.Close(); err != nil {
		t.Fatal(err)
	}

	snaps, err := wal.ValidSnapshotEntries(lg, wd)
	if err != nil {
		t.Fatal(err)
	}
	newest := snaps[len(snaps)-1]
	if newest.GetIndex() != 3 {
		t.Fatalf("newest valid snapshot record %d, want 3 (the record at 10 is above the commit)", newest.GetIndex())
	}
	w2, err := wal.Open(lg, wd, newest)
	if err != nil {
		t.Fatal(err)
	}
	defer w2.Close()
	_, st, es, err := w2.ReadAll()
	if err != nil {
		t.Fatalf("ReadAll: %v (want nil)", err)
	}
	var idx []uint64
	for _, e := range es {
		idx = append(idx, e.GetIndex())
	}
	if st.GetCommit() != 5 || len(idx) != 2 || idx[0] != 4 || idx[1] != 5 {
		t.Fatalf("ReadAll: commit %d entries %v, want commit 5 entries [4 5]", st.GetCommit(), idx)
	}
	t.Logf("valid snapshots %d, newest %d; ReadAll err=nil commit %d entries %v; the eager fold's base would be 10",
		len(snaps), newest.GetIndex(), st.GetCommit(), idx)
}
