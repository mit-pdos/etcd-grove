package raft

import (
	"testing"

	"github.com/stretchr/testify/require"
	pb "go.etcd.io/raft/v3/raftpb"
)

func TestSharedWitnessCommitsWithOneHalfMissingAVoter(t *testing.T) {
	large := []uint64{1, 3, 4, 5, 6}
	small := []uint64{1, 2, 5}
	for _, tc := range []struct {
		name    string
		in, out []uint64
	}{
		{"outgoing-needs-witness", large, small},
		{"incoming-needs-witness", small, large},
	} {
		t.Run(tc.name, func(t *testing.T) {
			cs := &pb.ConfState{Voters: tc.in, VotersOutgoing: tc.out,
				Witness: new(uint64(5)), WitnessOutgoing: new(uint64(5))}
			s := NewMemoryStorage()
			require.NoError(t, s.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
				Index: new(uint64(1)), Term: new(uint64(1)), ConfState: cs,
			}}))
			r := newTestRaft(1, 10, 1, s)
			r.becomeCandidate()
			r.becomeLeader()
			for id, pr := range r.trk.Progress {
				pr.RecentActive = id != 2
			}
			r.maybeStartNewSubterm(false, false)
			require.NoError(t, r.Step(&pb.Message{Type: pb.MsgProp.Enum(), From: new(r.id),
				To: new(r.id), Entries: []*pb.Entry{{Data: []byte("joint configuration")}}}))
			idx := r.raftLog.lastIndex()
			r.advanceMessagesAfterAppend()
			for _, id := range []uint64{3, 4, 6} {
				require.NoError(t, r.Step(&pb.Message{Type: pb.MsgAppResp.Enum(), From: new(id),
					To: new(r.id), Term: new(r.Term), Index: new(idx)}))
			}
			w := NewWitness(WitnessConfig{ID: 5, Storage: &memWitnessStorage{}, CheckQuorum: true})
			for _, m := range r.witnessMsgs {
				resp, err := w.Process(m)
				require.NoError(t, err)
				if resp != nil {
					require.NoError(t, r.Step(resp))
				}
			}
			require.GreaterOrEqual(t, r.raftLog.committed, idx,
				"the large half has a regular majority; the small half has voter 1 and the live witness")
		})
	}
}
