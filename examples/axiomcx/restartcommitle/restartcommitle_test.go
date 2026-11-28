// Package restartcommitle is the Go evidence for notes/axiom-review/bootstrap-restart-commitle.md (C1 of
// the etcd_safe lead, #50, 2026-11-28): with the eager-fold conjunct (walfiles-fold, restarteagerfold),
// walFiles (WalRecs.lean) still admitted WAL histories that wal.Open + ReadAll read back differently from
// the model's eager fold (walFoldChkFrom walFresh): those with a Save whose commit is above the last
// index at that point. The model's SaveSnapshot above the commit drops every entry (walSaveSnap: ents
// := []), the real WAL keeps reading the entries after the snapshot record. At the etcd pin d26dd5da6f
// (examples/go.mod).
//
// What it shows (TestCommitAboveLast): after Save(hs{Term 1, Commit 1}, entries 1..6), SaveSnapshot(3),
// Save(hs{Term 1, Commit 4}, []), SaveSnapshot(4), Close:
//   - the eager fold: SaveSnapshot(3) is above the commit 1, so the records are base 3 with no entries;
//     Save(commit 4) leaves commit 4 above the last index 3; SaveSnapshot(4) gives base 4, no entries;
//   - ValidSnapshotEntries keeps the record at 4 (at the commit 4), and Open(4) + ReadAll returns
//     err = nil, commit 4, entries [5 6].
// Raft's node loop never writes the third call (its Ready keeps committed <= lastIndex); the fix carries
// that in walRecs/walFiles (walCommitLeFrom) and makes Save's law require it (WalSaveCommitLe).
//
// Run: cd examples && go test ./axiomcx/restartcommitle/ -v
package restartcommitle

import (
	"testing"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"go.uber.org/zap"
)

func u(x uint64) *uint64 { return &x }

func TestCommitAboveLast(t *testing.T) {
	wd := t.TempDir() + "/wal"
	lg := zap.NewNop()
	w, err := wal.Create(lg, wd, []byte("md"))
	if err != nil {
		t.Fatal(err)
	}
	var ents []*raftpb.Entry
	for i := uint64(1); i <= 6; i++ {
		ents = append(ents, &raftpb.Entry{Index: u(i), Term: u(1)})
	}
	if err := w.Save(&raftpb.HardState{Term: u(1), Commit: u(1)}, ents); err != nil {
		t.Fatal(err)
	}
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: u(3), Term: u(1), ConfState: &raftpb.ConfState{}}); err != nil {
		t.Fatal(err)
	}
	// commit 4 above the eager fold's last index 3 (raft's node loop never saves this)
	if err := w.Save(&raftpb.HardState{Term: u(1), Commit: u(4)}, nil); err != nil {
		t.Fatal(err)
	}
	if err := w.SaveSnapshot(&walpb.Snapshot{Index: u(4), Term: u(1), ConfState: &raftpb.ConfState{}}); err != nil {
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
	if newest.GetIndex() != 4 {
		t.Fatalf("newest valid snapshot record %d, want 4", newest.GetIndex())
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
	if st.GetCommit() != 4 || len(idx) != 2 || idx[0] != 5 || idx[1] != 6 {
		t.Fatalf("ReadAll: commit %d entries %v, want commit 4 entries [5 6]", st.GetCommit(), idx)
	}
	t.Logf("newest valid snapshot %d; ReadAll err=nil commit %d entries %v; the eager fold has base 4 and no entries",
		newest.GetIndex(), st.GetCommit(), idx)
}
