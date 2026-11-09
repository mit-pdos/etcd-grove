// Package raftconf holds the requirement snippets of raft's tracker, quorum and confchange
// packages (batch R4, Spec/go_etcd_io/raft/v3/{tracker,quorum,confchange}/): minimal uses of the
// patterns raft's core, raft's read-index queue and this repository's examples rely on, each
// reliance an explicit panic.
package raftconf

import (
	"go.etcd.io/raft/v3/quorum"
)

// acks is an AckedIndexer over a plain map: a voter not in it has acknowledged nothing.
type acks map[uint64]uint64

// AckedIndex implements quorum.AckedIndexer.
func (a acks) AckedIndex(id uint64) (quorum.Index, bool) {
	i, ok := a[id]
	return quorum.Index(i), ok
}

// REQ raftconf/joint-committed: a joint quorum index is acknowledged by a strict majority of each
// non-empty half (raft's commit rule and its read-index confirmation).
// Users: tracker/tracker.go:162 (ProgressTracker.Committed, for raft.maybeCommit raft.go:796),
// read_only.go:81 (readOnly.maybeAdvance).
// Assumes: each half has at most 2^62 voters.
// Specs: JointConfig.CommittedIndex.spec; laws: jointIdx_quorum.spec.
func ReqJointCommitted(c quorum.JointConfig, a acks) {
	idx := uint64(c.CommittedIndex(a))
	for _, half := range c {
		if len(half) == 0 {
			continue
		}
		n := 0
		for id := range half {
			if a[id] >= idx {
				n++
			}
		}
		if 2*n <= len(half) {
			panic("joint-committed: index not acknowledged by a majority")
		}
	}
}

// REQ raftconf/joint-vote: a joint vote is won only with a majority of granted votes in each half,
// and is lost as soon as one half can no longer reach a majority (raft's elections, CheckQuorum).
// Users: tracker/tracker.go:252 (TallyVotes, for raft.poll raft.go:1100), tracker/tracker.go:192
// (QuorumActive).
// Specs: JointConfig.VoteResult.spec (the model's jointVote, majVote).
func ReqJointVote(c quorum.JointConfig, votes map[uint64]bool) {
	r := c.VoteResult(votes)
	for _, half := range c {
		if len(half) == 0 {
			continue
		}
		yes, notNo := 0, 0
		for id := range half {
			v, ok := votes[id]
			if ok && v {
				yes++
			}
			if !ok || v {
				notNo++
			}
		}
		if r == quorum.VoteWon && 2*yes <= len(half) {
			panic("joint-vote: won without a majority of a half")
		}
		if 2*notNo <= len(half) && r != quorum.VoteLost {
			panic("joint-vote: not lost though a half cannot win")
		}
	}
}

// REQ raftconf/empty-half: a joint configuration with an empty outgoing half decides as its
// incoming half alone (a configuration that is not joint).
// Users: every non-joint tracker (tracker.Config.Voters[1] is nil outside joint consensus).
// Assumes: m has at most 2^62 voters.
// Specs: JointConfig.CommittedIndex.spec, MajorityConfig.CommittedIndex.spec,
// JointConfig.VoteResult.spec, MajorityConfig.VoteResult.spec.
func ReqEmptyHalf(m quorum.MajorityConfig, a acks, votes map[uint64]bool) {
	c := quorum.JointConfig{m, nil}
	if c.CommittedIndex(a) != m.CommittedIndex(a) {
		panic("empty-half: committed index differs")
	}
	if c.VoteResult(votes) != m.VoteResult(votes) {
		panic("empty-half: vote result differs")
	}
}
