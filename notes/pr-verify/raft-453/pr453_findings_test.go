package raft

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A batch holding a normal entry and a conf change that is refused: Step reports
// ErrConfChangeRejected, yet the whole batch -- the normal entry included -- was appended.
func TestPR453BatchWithRejectedConfChange(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	r.becomeCandidate()
	r.becomeLeader()
	require.NoError(t, r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgProp.Enum(),
		Entries: []*pb.Entry{{Type: pb.EntryConfChange.Enum()}}}))
	last := r.raftLog.lastIndex()

	err := r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgProp.Enum(),
		Entries: []*pb.Entry{{Data: []byte("x")}, {Type: pb.EntryConfChange.Enum()}}})
	require.Equal(t, ErrConfChangeRejected, err)

	ents, err := r.raftLog.entries(last+1, noLimit)
	require.NoError(t, err)
	require.Len(t, ents, 2)
	require.Equal(t, []byte("x"), ents[0].GetData())
	require.Equal(t, pb.EntryNormal, ents[1].GetType())
}

// Node.ProposeConfChange does not wait for the proposal's result (Node.Step), so a refused
// conf change still returns nil to Node users; only RawNode.ProposeConfChange sees the error.
func TestPR453NodeProposeConfChangeRejectedReturnsNil(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	cfg := newTestConfig(1, 10, 1, s)
	ctx, cancel, n := newNodeTestHarness(t.Context(), t, cfg)
	defer cancel()
	require.NoError(t, n.Campaign(ctx))
	for {
		rd := <-n.Ready()
		require.NoError(t, s.Append(rd.Entries))
		n.Advance()
		if rd.SoftState != nil && rd.SoftState.RaftState == StateLeader {
			break
		}
	}
	cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))}
	require.NoError(t, n.ProposeConfChange(ctx, cc))
	// The first change is not applied yet: this one is refused, and yet...
	require.NoError(t, n.ProposeConfChange(ctx, cc))

	// ... it was: the log ends with the conf change and the empty entry that replaced the second.
	var got []*pb.Entry
	for len(got) < 2 {
		rd := <-n.Ready()
		require.NoError(t, s.Append(rd.Entries))
		for _, e := range rd.Entries {
			if e.GetType() == pb.EntryConfChange || (e.GetType() == pb.EntryNormal && len(got) > 0) {
				got = append(got, e)
			}
		}
		n.Advance()
	}
	require.Equal(t, pb.EntryConfChange, got[0].GetType())
	require.Equal(t, pb.EntryNormal, got[1].GetType())
	require.Empty(t, got[1].GetData())

	// RawNode.ProposeConfChange, by contrast, returns the error.
	rn, err := NewRawNode(newTestConfig(1, 10, 1, newTestMemoryStorage(withPeers(1))))
	require.NoError(t, err)
	require.NoError(t, rn.Campaign())
	for rn.HasReady() {
		rd := rn.Ready()
		require.NoError(t, rn.raft.raftLog.storage.(*MemoryStorage).Append(rd.Entries))
		rn.Advance(rd)
	}
	require.NoError(t, rn.ProposeConfChange(cc))
	require.Equal(t, ErrConfChangeRejected, rn.ProposeConfChange(cc))
}
