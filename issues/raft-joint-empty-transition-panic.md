---
upstream: none
checked: 2026-10-16
links:
candidate: issues/upstream/raft-joint-empty-transition-panic/
---

# raft: an empty `ConfChangeV2` with a non-`Auto` transition is accepted while joint, then panics every node that applies it

- **Status**: open (not reported upstream).
- **Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):
  - `raft.go:1313-1331` (`stepLeader`, `MsgProp`): at a joint configuration a conf change is
    refused unless `wantsLeaveJoint := len(cc.AsV2().Changes) == 0`; the `Transition` is not
    looked at.
  - `raftpb/confchange.go:109-113` (`ConfChangeV2.LeaveJoint`): true only for the zero
    `ConfChangeV2` (`Context` aside), so a `Transition` other than `Auto` (0) makes it false.
  - `raft.go:1939-1950` (`applyConfChange`): not `LeaveJoint`, so `cc.EnterJoint()`, which is
    `ok` for any non-`Auto` transition (`raftpb/confchange.go:89`), so
    `Changer.EnterJoint` (`confchange/confchange.go:51-58`), which fails with "config is
    already joint"; `applyConfChange` then `panic(err)`s.
  - The documentation (`raftpb/raft.proto:198-200`, on `ConfChangeV2`) says that leaving the
    joint configuration "is accomplished by proposing a ConfChangeV2 with only and optionally
    the Context field populated": the entry below is not such a proposal, but `stepLeader`
    takes it for one, and nothing says what becomes of it.
- **What happens**: at a joint configuration with nothing pending, the leader accepts
  `ConfChangeV2{Transition: ConfChangeTransitionJointExplicit}` (or `JointImplicit`) with no
  changes and appends it as an `EntryConfChangeV2`; it is committed; `ApplyConfChange` on it
  panics with "config is already joint". Every node applies the same committed entry, so
  every node panics, and again on every restart. (At a non-joint configuration the same
  proposal is refused: `!alreadyJoint && wantsLeaveJoint`.) Reproduction (in package `raft`,
  internal fields read only to know when the configuration is joint):

  ```go
  package raft

  import (
  	"testing"

  	pb "go.etcd.io/raft/v3/raftpb"
  )

  func TestEmptyNonAutoConfChangeAtJointPanics(t *testing.T) {
  	s := newTestMemoryStorage(withPeers(1))
  	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
  	if err != nil {
  		t.Fatal(err)
  	}
  	if err := rn.Campaign(); err != nil {
  		t.Fatal(err)
  	}
  	for rn.raft.state != StateLeader {
  		rd := rn.Ready()
  		s.Append(rd.Entries)
  		rn.Advance(rd)
  	}
  	// Enter a joint configuration explicitly (no auto-leave): add learner 2.
  	enter := pb.ConfChangeV2{
  		Transition: pb.ConfChangeTransitionJointExplicit,
  		Changes:    []pb.ConfChangeSingle{{Type: pb.ConfChangeAddLearnerNode, NodeId: 2}},
  	}
  	if err := rn.ProposeConfChange(enter); err != nil {
  		t.Fatal(err)
  	}
  	proposedBad := false
  	for i := 0; i < 20; i++ {
  		rd := rn.Ready()
  		s.Append(rd.Entries)
  		for _, e := range rd.CommittedEntries {
  			if e.Type != pb.EntryConfChangeV2 {
  				continue
  			}
  			var cc pb.ConfChangeV2
  			if err := cc.Unmarshal(e.Data); err != nil {
  				t.Fatal(err)
  			}
  			if len(cc.Changes) > 0 {
  				cs := rn.ApplyConfChange(cc) // applied before Advance
  				t.Logf("applied %v: ConfState %v", cc, cs)
  				continue
  			}
  			defer func() {
  				if r := recover(); r != nil {
  					t.Logf("PANIC reproduced: ApplyConfChange(%v): %v", cc, r)
  				} else {
  					t.Fatalf("no panic")
  				}
  			}()
  			rn.ApplyConfChange(cc)
  			return
  		}
  		rn.Advance(rd)
  		if !proposedBad && len(rn.raft.trk.Config.Voters[1]) > 0 &&
  			rn.raft.raftLog.applied >= rn.raft.pendingConfIndex {
  			bad := pb.ConfChangeV2{Transition: pb.ConfChangeTransitionJointExplicit}
  			if err := rn.ProposeConfChange(bad); err != nil {
  				t.Fatalf("proposal refused: %v", err)
  			}
  			last := rn.raft.raftLog.lastIndex()
  			ents, err := rn.raft.raftLog.entries(last, noLimit)
  			if err != nil || len(ents) != 1 || ents[0].Type != pb.EntryConfChangeV2 {
  				t.Fatalf("the leader replaced the proposal: %v %v", ents, err)
  			}
  			t.Logf("leader accepted %v at index %d", bad, last)
  			proposedBad = true
  		}
  	}
  	t.Fatal("the empty conf change was never committed")
  }
  ```

  Output (go1.26, at the pinned revision):

      applied {ConfChangeTransitionJointExplicit [{ConfChangeAddLearnerNode 2}] []}: ConfState voters:1 learners:2 voters_outgoing:1
      leader accepted {ConfChangeTransitionJointExplicit [] []} at index 3
      PANIC reproduced: ApplyConfChange({ConfChangeTransitionJointExplicit [] []}): config is already joint

- **How it happens**: the leader and the apply side recognize a "leave joint" entry
  differently. `stepLeader` counts changes: at a joint configuration it accepts any proposal
  with none, whatever its `Transition`. `applyConfChange` leaves only if `LeaveJoint()` holds,
  which needs the whole message zero apart from `Context`. An empty proposal with
  `JointExplicit` or `JointImplicit` passes the first check and fails the second, so it goes
  to `EnterJoint` at a configuration that is already joint. The test above runs:

  1. Node 1 is the single voter and the leader.
  2. It proposes `ConfChangeV2{Transition: JointExplicit, Changes: [AddLearner 2]}`, which
     commits and is applied: the configuration is joint (`voters:1 learners:2
     voters_outgoing:1`), without auto-leave.
  3. With that change applied, nothing is pending. The application proposes
     `ConfChangeV2{Transition: JointExplicit}` with no changes, as its leave. In `stepLeader`
     `alreadyJoint` and `wantsLeaveJoint` are both true, so no check fails and the leader
     appends the entry (index 3).
  4. The entry commits. `ApplyConfChange` on it: `LeaveJoint()` is false (the `Transition` is
     not zero), `EnterJoint()` answers `ok` with `autoLeave = false`, and
     `Changer.EnterJoint` fails with "config is already joint".
  5. `applyConfChange` panics with that error. Every node applies the same entry, so every
     node panics, and again on every restart.

  ```go
  // raft.go:1312-1324 (etcd-io/raft 40f8be7)
  			if cc != nil {
  				alreadyPending := r.pendingConfIndex > r.raftLog.applied
  				alreadyJoint := len(r.trk.Config.Voters[1]) > 0
  				wantsLeaveJoint := len(cc.AsV2().Changes) == 0 // <- only the number of changes

  				var failedCheck string
  				if alreadyPending {
  					failedCheck = fmt.Sprintf("possible unapplied conf change at index %d (applied to %d)", r.pendingConfIndex, r.raftLog.applied)
  				} else if alreadyJoint && !wantsLeaveJoint { // <-
  					failedCheck = "must transition out of joint config first"
  				} else if !alreadyJoint && wantsLeaveJoint {
  					failedCheck = "not in joint state; refusing empty conf change"
  				}
  ```

  ```go
  // raftpb/confchange.go:109-113 and raft.go:1939-1956 (etcd-io/raft 40f8be7)
  func (c ConfChangeV2) LeaveJoint() bool {
  	// NB: c is already a copy.
  	c.Context = nil
  	return proto.Equal(&c, &ConfChangeV2{}) // <-
  }

  func (r *raft) applyConfChange(cc pb.ConfChangeV2) pb.ConfState {
  	cfg, trk, err := func() (tracker.Config, tracker.ProgressMap, error) {
  		// ...
  		if cc.LeaveJoint() {
  			return changer.LeaveJoint()
  		} else if autoLeave, ok := cc.EnterJoint(); ok { // <-
  			return changer.EnterJoint(autoLeave, cc.Changes...)
  		}
  		return changer.Simple(cc.Changes...)
  	}()

  	if err != nil {
  		// TODO(tbg): return the error to the caller.
  		panic(err) // <-
  	}
  ```

  etcd cannot reach it: it proposes only v1 `raftpb.ConfChange`s (`EtcdServer.configure`),
  whose `AsV2()` has one change and the `Auto` transition, so it never enters a joint
  configuration, and its apply loop panics on any `EntryConfChangeV2` anyway ("unknown entry
  type"). raft v3.7.0 has the same bug: there `LeaveJoint` is `Transition == Auto &&
  len(Changes) == 0`, and `stepLeader` still tests only the length.

- **Expected**: the proposal is refused (replaced by an empty normal entry, as `stepLeader`
  does for the conf changes it refuses), since it is not the documented leave proposal:
  `stepLeader`'s joint check should agree with what `applyConfChange` will do, accepting an
  entry as leaving the joint configuration only if `LeaveJoint()` holds of it.
- **How the proof handles it**: `ccApplyM` (`InvApplyConf.lean`) is `EnterJoint` here, which
  answers `none` at a joint configuration: `raft.applyConfChange.spec` and
  `RawNode.ApplyConfChange.spec` require `ccApplyM ... = some _` (`CCApplies`), and the
  protocol-level configuration `cfgFold` (`Protocol/CfgOverlap.lean`) is `none` past such an
  entry, so no node of the safety argument applies it. `stepLeader`'s joint-configuration
  validation (`propConf`, `CCModel.lean`) is not specified yet (stage A2's "Left"); when it
  is, its spec will accept this entry, as the code does.
- **The same class, not reproduced**: `stepLeader` checks only "one pending change" and the
  joint/leave shape; the `Changer`'s own errors are found only at apply time, every one a
  panic of every node. E.g. a `ConfChange{Type: RemoveNode}` of the last incoming voter
  ("removed all voters", `confchange/confchange.go:171`). That one is the application's to
  avoid (etcd's server validates membership changes before proposing them), but nothing in
  raft's documentation says that a committed conf change must be valid for the
  configuration it applies to.
- **Possible fixes**: in `stepLeader`, `wantsLeaveJoint := cc.AsV2().LeaveJoint()` (refusing
  any other empty change), or run the `Changer` on the leader's configuration and refuse the
  entry on an error; or return the error from `applyConfChange` (its `TODO(tbg)`).
- **Found**: 2026-10-14, reconfiguration stage B1 (the protocol-level safety analysis,
  `notes/reconfiguration-safety.md`), checking which committed conf entries make `cfgFold`
  fail; reproduced by the test above.
