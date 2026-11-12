package raftconf

import (
	"go.etcd.io/raft/v3/confchange"
	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// REQ raftconf/quorum-active: CheckQuorum keeps a leader exactly while its recently active voters
// are a joint quorum (it clears the flags after each check).
// Users: raft.go:1300-1310 (stepLeader's MsgCheckQuorum: QuorumActive, then Visit clearing
// RecentActive).
// Specs: Restore.spec, ProgressTracker.Visit.spec, ProgressTracker.QuorumActive.spec; laws:
// Quorum.jointVote_won.spec.
func ReqQuorumActive() {
	trk, ok := restored(&pb.ConfState{Voters: []uint64{1, 2, 3}}, 1)
	if !ok {
		panic("quorum-active: three voters refused")
	}
	if !trk.QuorumActive() {
		panic("quorum-active: new peers are recently active")
	}
	trk.Visit(func(id uint64, pr *tracker.Progress) {
		if id != 1 {
			pr.RecentActive = false
		}
	})
	if trk.QuorumActive() {
		panic("quorum-active: one active voter of three is a quorum")
	}
	trk.Progress[2].RecentActive = true
	if !trk.QuorumActive() {
		panic("quorum-active: two active voters of three are no quorum")
	}
}

// REQ raftconf/learner-flag: a tracked peer is a learner iff its IsLearner is set, and a tracked
// peer that is not a learner is a voter of one half (a staged learner is still an outgoing voter).
// Users: raft.go:1992 (switchToConfig: r.isLearner), raft.go:1948 (promotable), node.go:395 and
// rawnode.go:121 (an untracked sender), raft.go:1652 (a learner's MsgAppResp).
// Assumes: cs lists at most 2^62 ids.
// Specs: Restore.spec, Changer.EnterJoint.spec (TrackerOk of the result),
// ProgressTracker.LearnerNodes.spec (the learners read through it: raft never reads the Learners
// map directly); laws: configOwn_valid.spec (Membership.Valid: staged learners are outgoing
// voters), configOwn_open.spec.
func ReqLearnerFlag(cs *pb.ConfState) {
	trk, ok := restored(cs, 1)
	if !ok {
		return
	}
	if len(trk.Voters[0]) > 0 && len(trk.Voters[1]) == 0 {
		// enter a joint configuration demoting a voter: it is staged, still an outgoing voter
		var id uint64
		for v := range trk.Voters[0] {
			id = v
			break
		}
		cfg, prs, err := confchange.Changer{Tracker: trk, LastIndex: 1}.EnterJoint(false,
			single(pb.ConfChangeAddLearnerNode, id))
		if err == nil {
			trk.Config, trk.Progress = cfg, prs
		}
	}
	learners := trk.LearnerNodes()
	for id, pr := range trk.Progress {
		l := contains(learners, id)
		_, v0 := trk.Voters[0][id]
		_, v1 := trk.Voters[1][id]
		if pr.IsLearner != l {
			panic("learner-flag: IsLearner is not membership in Learners")
		}
		if !pr.IsLearner && !v0 && !v1 {
			panic("learner-flag: a tracked non-learner that is no voter")
		}
		if pr.IsLearner && (v0 || v1) {
			panic("learner-flag: a learner that is a voter")
		}
	}
}

// REQ raftconf/voter-reads: raft reads the voters directly (the incoming map, IDs, IsSingleton,
// VoterNodes) and they agree.
// Users: raft.go:2153 (Voters[0][r.id] with IsSingleton: the read-index shortcut), raft.go:1063,
// 2031 (Voters.IDs()), raft.go:490 (VoterNodes).
// Assumes: cs lists at most 2^62 ids.
// Specs: Restore.spec, ProgressTracker.IsSingleton.spec, JointConfig.IDs.spec,
// ProgressTracker.VoterNodes.spec; laws: configOwn_open.spec.
func ReqVoterReads(cs *pb.ConfState) {
	trk, ok := restored(cs, 1)
	if !ok {
		return
	}
	ids := trk.Voters.IDs()
	nodes := trk.VoterNodes()
	if len(nodes) != len(ids) {
		panic("voter-reads: VoterNodes and IDs disagree")
	}
	for i, id := range nodes {
		if _, ok := ids[id]; !ok || (i > 0 && nodes[i-1] >= id) {
			panic("voter-reads: VoterNodes not the sorted voters")
		}
	}
	single := trk.IsSingleton()
	for id := range trk.Voters[0] {
		if _, ok := ids[id]; !ok {
			panic("voter-reads: an incoming voter missing from IDs")
		}
		if single && (len(ids) != 1 || len(trk.Voters[1]) != 0) {
			panic("voter-reads: a singleton with other voters")
		}
	}
}

// REQ raftconf/progress-copy: Status's copy of a Progress has its own ring (getProgressCopy).
// Users: status.go:46-50 (getProgressCopy); etcd's server.go:1615 (isLearnerReady reads Match).
// Specs: Inflights.Clone.spec, Inflights.Full.spec, Inflights.Add.spec, Inflights.Count.spec.
func ReqProgressCopy(pr *tracker.Progress) tracker.Progress {
	p := *pr
	p.Inflights = pr.Inflights.Clone()
	n := pr.Inflights.Count()
	if !p.Inflights.Full() {
		p.Inflights.Add(p.Next, 1)
		if pr.Inflights.Count() != n {
			panic("progress-copy: the copy shares the ring")
		}
	}
	return p
}

// contains reports whether x is in xs (a plain loop: the snippets use no unspecified library call).
func contains(xs []uint64, x uint64) bool {
	for _, y := range xs {
		if y == x {
			return true
		}
	}
	return false
}
