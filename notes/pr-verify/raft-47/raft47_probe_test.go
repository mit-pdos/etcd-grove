// Probes for etcd-io/raft#47 ("raft: fix out-of-order terms"), package raft.
//
// Both probes put raft in a state that the verified model excludes (a log whose last term is
// above the node's term; a snapshot of a term above the node's term) and show what the code
// does there: on the PR they pass, on the base without the PR they fail and print what the old
// code did.
package raft

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestProbeRaft47InconsistentStorage: a single voter restarted from a storage whose HardState
// term (1) is below its last entry's term (3) wins its election at term 2, through the public
// RawNode API. With raft#47 becomeLeader's appendEntry panics ("appending out-of-order term");
// without it the leader appends its empty entry at term 2 after the term-3 entry.
func TestProbeRaft47InconsistentStorage(t *testing.T) {
	storage := newTestMemoryStorage(withPeers(1))
	require.NoError(t, storage.SetHardState(&pb.HardState{Term: new(uint64(1)), Commit: new(uint64(0))}))
	require.NoError(t, storage.Append(index(1).terms(1, 2, 3)))
	rn := newTestRawNode(1, 10, 1, storage)

	var panicked any
	func() {
		defer func() { panicked = recover() }()
		require.NoError(t, rn.Campaign())
		for i := 0; i < 3 && rn.HasReady(); i++ {
			rd := rn.Ready()
			require.NoError(t, storage.Append(rd.Entries))
			rn.Advance(rd)
		}
	}()
	if panicked == nil {
		last := rn.raft.raftLog.lastIndex()
		var terms []uint64
		for i := uint64(1); i <= last; i++ {
			terms = append(terms, mustTerm(rn.raft.raftLog.term(i)))
		}
		t.Fatalf("no panic: state %v at term %d, log terms %v", rn.raft.state, rn.raft.Term, terms)
	}
	t.Logf("panicked: %v", panicked)
}

// TestProbeRaft47SnapshotHigherTerm: restore of a snapshot at term 11 by a follower at term 2.
// With raft#47 it is refused and the node steps down to term 11; without it the snapshot is
// restored and the node stays at term 2, its log's last term (11) above its term.
func TestProbeRaft47SnapshotHigherTerm(t *testing.T) {
	s := &pb.Snapshot{
		Metadata: &pb.SnapshotMetadata{
			Index:     new(uint64(11)),
			Term:      new(uint64(11)),
			ConfState: &pb.ConfState{Voters: []uint64{1, 2}},
		},
	}
	sm := newTestRaft(2, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	sm.becomeFollower(2, 1)
	ok := sm.restore(s)
	require.False(t, ok, "restored at term %d, log last term %d", sm.Term, sm.raftLog.lastEntryID().term)
	require.Equal(t, uint64(11), sm.Term)
	require.Equal(t, StateFollower, sm.state)
	require.Equal(t, None, sm.lead)
}
