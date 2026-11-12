package raftconf

import (
	"go.etcd.io/raft/v3/confchange"
	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// restored builds a tracker at the configuration cs lists, as raft's newRaft does; ok is false if
// confchange refuses cs.
func restored(cs *pb.ConfState, lastIndex uint64) (trk tracker.ProgressTracker, ok bool) {
	trk = tracker.MakeProgressTracker(4, 0)
	cfg, prs, err := confchange.Restore(confchange.Changer{Tracker: trk, LastIndex: lastIndex}, cs)
	if err != nil {
		return trk, false
	}
	trk.Config = cfg
	trk.Progress = prs
	return trk, true
}

// REQ raftconf/committed-quorum: the tracker's committed index is matched by a strict majority of
// each half of the voters (raft's commit safety).
// Users: raft.go:796 (raft.maybeCommit).
// Assumes: cs lists at most 2^62 ids.
// Specs: MakeProgressTracker.spec, Restore.spec, Progress.MaybeUpdate.spec,
// ProgressTracker.Committed.spec; laws: Quorum.jointIdx_quorum.spec, configOwn_open.spec.
func ReqCommittedQuorum(cs *pb.ConfState, acked map[uint64]uint64) {
	trk, ok := restored(cs, 1)
	if !ok {
		return
	}
	for id, pr := range trk.Progress {
		pr.MaybeUpdate(acked[id])
	}
	c := trk.Committed()
	for _, half := range trk.Voters {
		if len(half) == 0 {
			continue
		}
		n := 0
		for id := range half {
			if trk.Progress[id].Match >= c {
				n++
			}
		}
		if 2*n <= len(half) {
			panic("committed-quorum: committed index not matched by a majority")
		}
	}
}

// REQ raftconf/tally-votes: an election is won only with a majority of granted votes in each half;
// a voter's first vote counts.
// Users: raft.go:1099-1100 (raft.poll: RecordVote, TallyVotes), raft.go:812, 944 (ResetVotes).
// Assumes: cs lists at most 2^62 ids.
// Specs: ProgressTracker.ResetVotes.spec, RecordVote.spec, TallyVotes.spec.
func ReqTallyVotes(cs *pb.ConfState, votes map[uint64]bool) {
	trk, ok := restored(cs, 1)
	if !ok {
		return
	}
	trk.ResetVotes()
	for id, v := range votes {
		trk.RecordVote(id, v)
		trk.RecordVote(id, !v) // ignored: the first vote counts
	}
	_, _, res := trk.TallyVotes()
	if res != 3 { // quorum.VoteWon
		return
	}
	for _, half := range trk.Voters {
		if len(half) == 0 {
			continue
		}
		yes := 0
		for id := range half {
			if votes[id] {
				yes++
			}
		}
		if 2*yes <= len(half) {
			panic("tally-votes: won without a majority")
		}
	}
}

// REQ raftconf/visit-sorted: Visit calls back once per tracked peer, in increasing id order, with
// the peer's Progress, which the callback may read through the tracker and write.
// Users: raft.go:715, 729 (bcastAppend, bcastHeartbeat), 813 (reset), 1306 (CheckQuorum),
// 2023 (switchToConfig), status.go:46 (getProgressCopy), rawnode.go:517 (WithProgress).
// Assumes: cs lists at most 2^62 ids.
// Specs: ProgressTracker.Visit.spec.
func ReqVisitSorted(cs *pb.ConfState) {
	trk, ok := restored(cs, 1)
	if !ok {
		return
	}
	var last uint64
	first := true
	n := 0
	trk.Visit(func(id uint64, pr *tracker.Progress) {
		if !first && id <= last {
			panic("visit-sorted: not in increasing order")
		}
		if trk.Progress[id] != pr {
			panic("visit-sorted: not the peer's Progress")
		}
		pr.RecentActive = false
		first, last = false, id
		n++
	})
	if n != len(trk.Progress) {
		panic("visit-sorted: a peer missed")
	}
}

// REQ raftconf/inflights-full: a ring accepts messages up to its capacity, is then full, and
// frees the acknowledged ones oldest first.
// Users: tracker/progress.go:170 (SentEntries), raft.go:639 (maybeSendAppend), raft.go:1562
// (FreeLE on MsgAppResp).
// Specs: NewInflights.spec, Inflights.Add.spec, Inflights.Full.spec, Inflights.FreeLE.spec,
// Inflights.Count.spec.
func ReqInflightsFull() {
	in := tracker.NewInflights(2, 0)
	in.Add(1, 10)
	if in.Full() {
		panic("inflights-full: full below capacity")
	}
	in.Add(2, 10)
	if !in.Full() {
		panic("inflights-full: not full at capacity")
	}
	in.FreeLE(1)
	if in.Full() || in.Count() != 1 {
		panic("inflights-full: acknowledged message not freed")
	}
}

// REQ raftconf/progress-flow: the probe, replicate and snapshot transitions raft makes, and the
// flow control they imply (a probe sends one append at a time; a snapshot pauses the peer; a
// probe after a snapshot resumes past it).
// Users: raft.go:620, 659, 686, 966, 1521-1562, 1631-1648 (maybeSendAppend, maybeSendSnapshot,
// becomeLeader, stepLeader).
// Specs: Progress.IsPaused.spec, SentEntries.spec, MaybeUpdate.spec, BecomeReplicate.spec,
// BecomeSnapshot.spec, BecomeProbe.spec, NewInflights.spec.
func ReqProgressFlow() {
	pr := &tracker.Progress{Next: 1, Inflights: tracker.NewInflights(4, 0)}
	if pr.IsPaused() {
		panic("progress-flow: a new probe is paused")
	}
	pr.SentEntries(1, 10)
	if !pr.IsPaused() {
		panic("progress-flow: a probe sends more than one append")
	}
	if !pr.MaybeUpdate(1) || pr.Match != 1 || pr.Next != 2 || pr.IsPaused() {
		panic("progress-flow: an acknowledgement not recorded")
	}
	pr.BecomeReplicate()
	pr.SentEntries(2, 20)
	if pr.Next != 4 || pr.Inflights.Count() != 1 {
		panic("progress-flow: replicate does not pipeline")
	}
	pr.BecomeSnapshot(10)
	if !pr.IsPaused() || pr.Next != 11 {
		panic("progress-flow: snapshot does not pause")
	}
	pr.BecomeProbe()
	if pr.Next != 11 || pr.IsPaused() {
		panic("progress-flow: probe does not resume past the snapshot")
	}
}

// REQ raftconf/clone-fresh: a cloned configuration shares no map with the tracker's (raft hands
// it out in Status, the client's to keep).
// Users: status.go:74 (getStatus), confchange.go:283 (checkAndCopy).
// Assumes: cs lists at most 2^62 ids.
// Specs: Config.Clone.spec, JointConfig.IDs.spec; laws: configOwn_open.spec.
func ReqCloneFresh(cs *pb.ConfState) {
	trk, ok := restored(cs, 1)
	if !ok {
		return
	}
	n := len(trk.Voters[0])
	c := trk.Config.Clone()
	ids := c.Voters.IDs() // a fresh map: the deletes below do not write the map ranged over
	for id := range ids {
		delete(c.Voters[0], id)
	}
	if len(trk.Voters[0]) != n {
		panic("clone-fresh: the clone shares the tracker's voters")
	}
}
