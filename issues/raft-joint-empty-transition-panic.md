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
