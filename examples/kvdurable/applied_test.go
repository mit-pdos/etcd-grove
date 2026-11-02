package kvdurable

import (
	"testing"

	"go.etcd.io/raft/v3"
	pb "go.etcd.io/raft/v3/raftpb"
	"google.golang.org/protobuf/proto"
)

// TestAppliedAboveConfState reproduces nonissues/raft-applied-above-snapshot-confstate.md: a node
// restarted with Config.Applied above its storage's snapshot never re-applies the configuration
// changes between the two (raft returns no entry at or below Applied), so its configuration stays
// the snapshot's (InitialState's ConfState). Here the snapshot at 1 has the single voter 1, entry 2
// (committed, applied before the restart) adds voter 2; restarted with Applied = 2, node 1 still
// counts itself the only voter, and elects itself and commits alone, without node 2.
func TestAppliedAboveConfState(t *testing.T) {
	st := raft.NewMemoryStorage()
	st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(1)), Term: new(uint64(1)),
		ConfState: &pb.ConfState{Voters: []uint64{1}}}})
	cc, err := proto.Marshal(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))})
	if err != nil {
		t.Fatal(err)
	}
	st.Append([]*pb.Entry{{Term: new(uint64(1)), Index: new(uint64(2)), Type: pb.EntryConfChange.Enum(), Data: cc}})
	st.SetHardState(&pb.HardState{Term: new(uint64(1)), Vote: new(uint64(1)), Commit: new(uint64(2))})
	rn, err := raft.NewRawNode(&raft.Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: st, Applied: 2,
		MaxSizePerMsg: 1 << 20, MaxInflightMsgs: 256, Logger: quietLogger{}})
	if err != nil {
		t.Fatal(err)
	}
	if voters := rn.Status().Config.Voters.IDs(); len(voters) != 1 {
		t.Fatalf("voters %v: the issue is gone", voters)
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
	if s := rn.Status(); s.RaftState != raft.StateLeader {
		t.Fatalf("node 1 is %v, not leader alone", s.RaftState)
	}
}
