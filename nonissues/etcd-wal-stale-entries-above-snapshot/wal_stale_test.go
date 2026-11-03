package wal_test

import (
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// A follower's WAL holds entries 1..5 of term 1 (the last three uncommitted); it then receives a
// snapshot at index 3, term 2 (a new leader's), and saves it as etcd's raft loop does: SaveSnapshot,
// then Save(hardState, no entries). ReadAll from that snapshot returns the old entries 4..5.
func TestReadAllKeepsEntriesAboveLaterSnapshot(t *testing.T) {
	dir := t.TempDir()
	lg := zap.NewNop()
	w, err := wal.Create(lg, dir, nil)
	if err != nil {
		t.Fatal(err)
	}
	var ents []*raftpb.Entry
	for i := uint64(1); i <= 5; i++ {
		ents = append(ents, &raftpb.Entry{Index: proto.Uint64(i), Term: proto.Uint64(1)})
	}
	if err := w.Save(&raftpb.HardState{Term: proto.Uint64(1), Vote: proto.Uint64(1), Commit: proto.Uint64(2)}, ents); err != nil {
		t.Fatal(err)
	}
	snap := &walpb.Snapshot{Index: proto.Uint64(3), Term: proto.Uint64(2), ConfState: &raftpb.ConfState{Voters: []uint64{1}}}
	if err := w.SaveSnapshot(snap); err != nil {
		t.Fatal(err)
	}
	if err := w.Save(&raftpb.HardState{Term: proto.Uint64(2), Vote: proto.Uint64(0), Commit: proto.Uint64(3)}, nil); err != nil {
		t.Fatal(err)
	}
	w.Close()

	w2, err := wal.Open(lg, dir, snap)
	if err != nil {
		t.Fatal(err)
	}
	defer w2.Close()
	_, st, got, err := w2.ReadAll()
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range got {
		t.Logf("entry index %d term %d", e.GetIndex(), e.GetTerm())
	}
	t.Logf("hard state term %d commit %d", st.GetTerm(), st.GetCommit())
	if len(got) != 0 {
		t.Errorf("ReadAll after a snapshot at 3 (term 2) returned %d entries of the old log above it", len(got))
	}
}
