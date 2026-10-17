package raft

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A proposal whose batch holds a normal entry and a conf change that the leader
// refuses (one is already pending) returns ErrConfChangeRejected, but the normal
// entry was appended all the same (and the refused change replaced by an empty
// entry): the error does not mean that the proposal failed.
func TestPR454MixedBatchRejectedButAppended(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	require.NoError(t, err)
	require.NoError(t, rn.Campaign())
	for rn.raft.state != StateLeader {
		rd := rn.Ready()
		s.Append(rd.Entries)
		rn.Advance(rd)
	}
	// A first conf change: accepted, now pending (not applied).
	cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))}
	require.NoError(t, rn.ProposeConfChange(cc))
	last := rn.raft.raftLog.lastIndex()

	_, ccData, err := pb.MarshalConfChange(cc)
	require.NoError(t, err)
	err = rn.Step(&pb.Message{
		Type: pb.MsgProp.Enum(),
		From: new(uint64(1)),
		Entries: []*pb.Entry{
			{Data: []byte("payload")},
			{Type: pb.EntryConfChange.Enum(), Data: ccData},
		},
	})
	require.Equal(t, ErrConfChangeRejected, err)
	ents, err := rn.raft.raftLog.entries(last+1, noLimit)
	require.NoError(t, err)
	require.Len(t, ents, 2)
	require.Equal(t, []byte("payload"), ents[0].GetData()) // appended despite the error
	require.Equal(t, pb.EntryNormal, ents[1].GetType())     // the refused change, emptied

	// A second refused ProposeConfChange also returns the error, while the log
	// grows by an empty entry.
	last = rn.raft.raftLog.lastIndex()
	require.Equal(t, ErrConfChangeRejected, rn.ProposeConfChange(cc))
	require.Equal(t, last+1, rn.raft.raftLog.lastIndex())
}

// Through the Node API the new error is never seen: ProposeConfChange does not
// wait for the proposal's result.
func TestPR454NodeProposeConfChangeNoError(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	require.NoError(t, err)
	n := newNode(rn)
	r := rn.raft
	go n.run()
	defer n.Stop()
	n.Campaign(t.Context())
	for {
		rd := <-n.Ready()
		s.Append(rd.Entries)
		n.Advance()
		if rd.SoftState != nil && rd.SoftState.Lead == r.id {
			break
		}
	}
	cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))}
	require.NoError(t, n.ProposeConfChange(t.Context(), cc))
	// The first is pending (never applied here): the second is refused, silently.
	require.NoError(t, n.ProposeConfChange(t.Context(), cc))
}
