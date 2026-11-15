package raftconf

import (
	"slices"

	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/confchange"
	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

func single(t pb.ConfChangeType, id uint64) *pb.ConfChangeSingle {
	return &pb.ConfChangeSingle{Type: t.Enum(), NodeId: new(id)}
}

// validConf is examples/raft/kvreconf's pre-check (without its size bound): whether applying cc
// at the configuration cs lists succeeds, by the Changer method raft.applyConfChange picks.
func validConf(cs *pb.ConfState, cc *pb.ConfChangeV2) bool {
	trk, ok := restored(cs, 1)
	if !ok {
		return false
	}
	chg := confchange.Changer{Tracker: trk, LastIndex: 1}
	var err error
	if cc.LeaveJoint() {
		_, _, err = chg.LeaveJoint()
	} else if autoLeave, ok := cc.EnterJoint(); ok {
		_, _, err = chg.EnterJoint(autoLeave, cc.GetChanges()...)
	} else {
		_, _, err = chg.Simple(cc.GetChanges()...)
	}
	return err == nil
}

// REQ raftconf/apply-like-raft: a client's pre-check with confchange (Restore from the node's
// ConfState, then the Changer method raft would pick) succeeds only when raft's ApplyConfChange
// does not panic: the decision kvreconf takes on every committed conf entry, the same at every
// replica.
// Users: examples/raft/kvreconf/kv.go:219 (validConf), examples/raft/kvdurable/kv.go:228.
// Assumes: rn's configuration is the one cs lists (cs is what rn's last ApplyConfChange, or its
// start, gave), and cc's transition is a known one when it enters a joint configuration (raftpb's
// EnterJoint() panics otherwise, in the pre-check as in raft); cs lists at most 2^62 ids.
// Specs: Restore.spec, Changer.Simple.spec, Changer.EnterJoint.spec, Changer.LeaveJoint.spec,
// R1's RawNode.ApplyConfChange.spec (R1's Membership.applyChange is changeV2); laws:
// restore_lists.spec.
func ReqApplyLikeRaft(rn *raft.RawNode, cs *pb.ConfState, cc *pb.ConfChangeV2) *pb.ConfState {
	if !validConf(cs, cc) {
		return cs
	}
	return rn.ApplyConfChange(cc) // must not panic
}

// REQ raftconf/restore-empty: an empty ConfState restores to the empty configuration (a new
// cluster's node before its bootstrap entries, raft.go:472).
// Users: raft.go:472 (newRaft), raft.go:776 (appliedSnap).
// Specs: MakeProgressTracker.spec, Restore.spec.
func ReqRestoreEmpty() {
	cfg, prs, err := confchange.Restore(confchange.Changer{Tracker: tracker.MakeProgressTracker(1, 0)},
		&pb.ConfState{})
	if err != nil || len(cfg.Voters[0]) != 0 || len(cfg.Voters[1]) != 0 || len(prs) != 0 {
		panic("restore-empty: not the empty configuration")
	}
}

// REQ raftconf/restore-roundtrip: the ConfState of a configuration restores to that configuration
// (raft's restart and snapshot round-trip check, assertConfStatesEquivalent).
// Users: raft.go:472-479 (newRaft), raft.go:776-787 (appliedSnap).
// Assumes: cs lists at most 2^62 ids.
// Specs: Restore.spec, ProgressTracker.ConfState.spec; laws: restore_lists.spec,
// restore_valid.spec.
func ReqRestoreRoundTrip(cs *pb.ConfState) {
	trk, ok := restored(cs, 1)
	if !ok {
		return // a ConfState confchange refuses
	}
	cs2 := trk.ConfState()
	trk2, ok := restored(cs2, 1)
	if !ok {
		panic("restore-roundtrip: a configuration's own ConfState is refused")
	}
	cs3 := trk2.ConfState()
	if !slices.Equal(cs2.Voters, cs3.Voters) || !slices.Equal(cs2.VotersOutgoing, cs3.VotersOutgoing) ||
		!slices.Equal(cs2.Learners, cs3.Learners) || !slices.Equal(cs2.LearnersNext, cs3.LearnersNext) ||
		cs2.GetAutoLeave() != cs3.GetAutoLeave() {
		panic("restore-roundtrip: restored to another configuration")
	}
}

// REQ raftconf/last-voter: removing the last voter is an error the Changer returns (raft panics on
// it in applyConfChange; a client's pre-check refuses it), not a panic in confchange.
// Users: examples/raft/kvreconf/kv.go:219 (validConf); raft.go:1963 (applyConfChange).
// Specs: Restore.spec, Changer.Simple.spec.
func ReqLastVoter() {
	trk, ok := restored(&pb.ConfState{Voters: []uint64{1}}, 1)
	if !ok {
		panic("last-voter: one voter refused")
	}
	_, _, err := confchange.Changer{Tracker: trk, LastIndex: 1}.Simple(single(pb.ConfChangeRemoveNode, 1))
	if err == nil {
		panic("last-voter: removed the last voter")
	}
}

// REQ raftconf/joint-cycle: entering a joint configuration keeps the old voters as the outgoing
// half; leaving it drops them (raft's joint consensus, examples/raft/kvreconf's v2 changes).
// Users: raft.go:1959-1961 (applyConfChange), examples/raft/kvreconf/reconf.go.
// Specs: Restore.spec, Changer.EnterJoint.spec, Changer.LeaveJoint.spec; laws: configOwn_open.spec.
func ReqJointCycle() {
	trk, ok := restored(&pb.ConfState{Voters: []uint64{1, 2, 3}}, 1)
	if !ok {
		panic("joint-cycle: three voters refused")
	}
	cfg, prs, err := confchange.Changer{Tracker: trk, LastIndex: 1}.EnterJoint(false,
		single(pb.ConfChangeAddNode, 4), single(pb.ConfChangeRemoveNode, 1))
	if err != nil || len(cfg.Voters[0]) != 3 || len(cfg.Voters[1]) != 3 {
		panic("joint-cycle: not joint")
	}
	trk.Config, trk.Progress = cfg, prs
	cfg, prs, err = confchange.Changer{Tracker: trk, LastIndex: 1}.LeaveJoint()
	if err != nil || len(cfg.Voters[0]) != 3 || len(cfg.Voters[1]) != 0 || len(prs) != 3 {
		panic("joint-cycle: not left")
	}
}
