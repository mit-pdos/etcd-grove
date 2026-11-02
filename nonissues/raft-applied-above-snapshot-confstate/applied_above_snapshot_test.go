package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// TestAppliedAboveSnapshotConfState: a node restarted with Config.Applied above its storage's
// snapshot never re-applies the configuration changes between the two (raft returns no entry at
// or below Applied), so its configuration stays the snapshot's (InitialState's ConfState). Here
// the snapshot at 1 has the single voter 1 and entry 2 (committed, applied before the restart)
// adds voter 2; restarted with Applied = 2, node 1 should count voters 1 and 2, but counts itself
// alone, and elects itself without node 2.
func TestAppliedAboveSnapshotConfState(t *testing.T) {
	st := NewMemoryStorage()
	st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(1)), Term: new(uint64(1)),
		ConfState: &pb.ConfState{Voters: []uint64{1}}}})
	cc, err := proto.Marshal(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))})
	if err != nil {
		t.Fatal(err)
	}
	st.Append([]*pb.Entry{{Term: new(uint64(1)), Index: new(uint64(2)), Type: pb.EntryConfChange.Enum(), Data: cc}})
	st.SetHardState(&pb.HardState{Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(uint64(2))})
	rn, err := NewRawNode(&Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: st, Applied: 2,
		MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, Logger: discardLogger})
	if err != nil {
		t.Fatal(err)
	}
	if voters := rn.Status().Config.Voters.IDs(); len(voters) != 2 {
		t.Errorf("voters %v after restarting with Applied = 2: want 1 and 2 (entry 2 added voter 2)", voters)
	}
	rn.Campaign()
	for rn.HasReady() {
		rd := rn.Ready()
		for _, e := range rd.CommittedEntries {
			if e.GetIndex() <= 2 {
				t.Fatalf("raft returned entry %d, at or below Applied", e.GetIndex())
			}
		}
		st.SetHardState(rd.HardState)
		st.Append(rd.Entries)
		rn.Advance(rd)
	}
	if s := rn.Status(); s.RaftState == StateLeader {
		t.Errorf("node 1 became leader without node 2's vote")
	}
}
