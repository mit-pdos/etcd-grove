/-
# raft's `confchange` package (batch R4): what a configuration change does

The pure transition of a configuration (`Tracker.Membership`) under confchange's `Changer`:
`simple`, `enterJoint`, `leaveJoint` (`none` exactly where the Go method returns an error), the
dispatch of a `ConfChangeV2` by its transition (`changeV2`: what `raft.applyConfChange` runs,
`none` also where raftpb's `EnterJoint()` panics on an unknown transition), and `restore` (a
`ConfState` replayed as `Restore` does). Transparent, no resources: the resources and laws are
`Api.lean`'s.

**Exact at a valid configuration.** Each function mirrors its Go method step by step on a tracker
that holds a valid configuration in canonical form, its progress map tracking exactly the
configuration's ids, each marked a learner iff it is one (`Tracker.TrackerOk`): there the
`IsLearner` marks confchange reads are the learner set, and the input check of `checkAndCopy`
passes, so neither appears here. The output check (`checkAndReturn`) is kept (`checked`).

**R1's `Membership.applyChange` is defined from `changeV2`** (R1's `Model.lean`, integration I2):
`.v1 cc` is `changeV2 ⟨TransitionAuto, [⟨cc.type, cc.nodeId⟩]⟩` (`ConfChange.AsV2()`: one change,
transition `Auto`), `.v2 c` is `changeV2 ⟨c.transition, c.changes⟩`; R1's `Membership` is
`Tracker.Membership` and its `ConfState.Is` is `Lists` of the five fields. A change is raftpb's
`ConfChangeSingle` (`Single` is its name here) and the enumerations are raftpb's values
(`raftpb/Model.lean`, which imports nothing of raft's).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.tracker.Model
public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Model

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Classical
open Tracker

/-- `raftpb.ConfChangeType`'s values (raftpb's). -/
abbrev AddNode : w32 := RaftPb.ConfChangeAddNode
abbrev RemoveNode : w32 := RaftPb.ConfChangeRemoveNode
abbrev UpdateNode : w32 := RaftPb.ConfChangeUpdateNode
abbrev AddLearnerNode : w32 := RaftPb.ConfChangeAddLearnerNode

/-- `raftpb.ConfChangeTransition`'s values (raftpb's). -/
abbrev TransitionAuto : w32 := RaftPb.ConfChangeTransitionAuto
abbrev TransitionJointImplicit : w32 := RaftPb.ConfChangeTransitionJointImplicit
abbrev TransitionJointExplicit : w32 := RaftPb.ConfChangeTransitionJointExplicit

/-- **One change**: raftpb's `ConfChangeSingle` (its getters' values: a missing field reads `0`).
(Integration I2: was this batch's own structure with the same fields.) -/
abbrev Single := RaftPb.ConfChangeSingle

/-- **A change** (`raftpb.ConfChangeV2` as `applyConfChange` reads it; its context is ignored). -/
structure V2 where
  transition : w32
  changes : List Single

/-! ## One change, as `Changer.apply` makes it -/

/-- `remove(id)`: out of the incoming voters and both learner sets (still tracked if an outgoing
voter). -/
def remove (id : w64) (m : Membership) : Membership :=
  { m with voters := m.voters \ {[id]}, learners := m.learners \ {[id]},
           learnersNext := m.learnersNext \ {[id]} }

/-- `makeVoter(id)`: an incoming voter, no longer a learner. -/
def makeVoter (id : w64) (m : Membership) : Membership :=
  { m with voters := m.voters ∪ {[id]}, learners := m.learners \ {[id]},
           learnersNext := m.learnersNext \ {[id]} }

/-- `makeLearner(id)`: a learner stays one; anyone else leaves the incoming voters and becomes a
learner, staged (`LearnersNext`) while an outgoing voter. -/
def makeLearner (id : w64) (m : Membership) : Membership :=
  if id ∈ m.learners then m
  else
    let m1 := remove id m
    if id ∈ m.votersOutgoing then { m1 with learnersNext := m1.learnersNext ∪ {[id]} }
    else { m1 with learners := m1.learners ∪ {[id]} }

/-- One change of `apply`'s loop: node `0` skipped (etcd's refusal); by type; an unknown type is
the error "unexpected conf type". -/
def applyOne (c : Single) (m : Membership) : Option Membership :=
  if c.nodeId = W64 0 then some m
  else if c.type = AddNode then some (makeVoter c.nodeId m)
  else if c.type = AddLearnerNode then some (makeLearner c.nodeId m)
  else if c.type = RemoveNode then some (remove c.nodeId m)
  else if c.type = UpdateNode then some m
  else none

/-- The changes in order; the first error stops them. -/
def applyAll : List Single → Membership → Option Membership
  | [], m => some m
  | c :: cs, m => (applyOne c m).bind (applyAll cs)

/-- `Changer.apply`: the changes, then the error "removed all voters" if no incoming voter is
left. -/
def apply (cs : List Single) (m : Membership) : Option Membership :=
  (applyAll cs m).bind fun m' => if m'.voters = ∅ then none else some m'

/-- `checkAndReturn`: the configuration if `checkInvariants` accepts it. -/
def checked (m : Membership) : Option Membership := if m.CfgOk then some m else none

/-- `Simple`'s check `symdiff(old, new) > 1`, on Go's `int` (it wraps past `2^63 - 1`: only for
sets no Go map holds). -/
def symdiffTooBig (l r : GSet w64) : Prop := 1 < sint.Z (W64 (GMap.size (l \ r) + GMap.size (r \ l)))

/-! ## The `Changer`'s transitions -/

/-- **`Changer.Simple(cs)`**: errors in a joint configuration, on `apply`'s errors, and when more
than one incoming voter changed. (`checkAndCopy`'s copy has `AutoLeave` off: `Config.Clone` does
not copy it; it is off anyway outside a joint configuration.) -/
def simple (cs : List Single) (m : Membership) : Option Membership :=
  if m.votersOutgoing ≠ ∅ then none
  else match apply cs { m with autoLeave := false } with
    | none => none
    | some m1 => if symdiffTooBig m.voters m1.voters then none else checked m1

/-- **`Changer.EnterJoint(autoLeave, cs)`**: errors in a joint configuration and in a voterless
one; the outgoing voters are the incoming ones; then `apply`, the auto-leave flag set. -/
def enterJoint (autoLeave : Bool) (cs : List Single) (m : Membership) : Option Membership :=
  if m.votersOutgoing ≠ ∅ then none
  else if m.voters = ∅ then none
  else match apply cs { m with votersOutgoing := m.voters, autoLeave := false } with
    | none => none
    | some m1 => checked { m1 with autoLeave := autoLeave }

/-- **`Changer.LeaveJoint()`**: errors outside a joint configuration; the staged learners become
learners, the outgoing voters go (untracked unless still incoming voters or learners). -/
def leaveJoint (m : Membership) : Option Membership :=
  if m.votersOutgoing = ∅ then none
  else checked { voters := m.voters, votersOutgoing := ∅, learners := m.learners ∪ m.learnersNext,
                 learnersNext := ∅, autoLeave := false }

/-- **What `raft.applyConfChange(c)` does to configuration `m`**: `LeaveJoint` for the zero change
(transition `Auto`, no changes); `EnterJoint` for a joint transition or several changes (auto-leave
for `Auto` and `JointImplicit`; `none` for an unknown transition, where raftpb's `EnterJoint()`
panics); `Simple` otherwise. `none` exactly where `raft.applyConfChange` panics (at a valid `m`). -/
def changeV2 (c : V2) (m : Membership) : Option Membership :=
  if c.transition = TransitionAuto ∧ c.changes = [] then leaveJoint m
  else if c.transition ≠ TransitionAuto ∨ 1 < c.changes.length then
    if c.transition = TransitionAuto ∨ c.transition = TransitionJointImplicit then
      enterJoint true c.changes m
    else if c.transition = TransitionJointExplicit then enterJoint false c.changes m
    else none
  else simple c.changes m

/-! ## `Restore` -/

/-- The changes, one `Simple` each, the first error stopping them (`chain`). -/
def simpleEach : List Single → Membership → Option Membership
  | [], m => some m
  | c :: cs, m => (simple [c] m).bind (simpleEach cs)

/-- **`Restore(chg, cs)`** from the changer's configuration `m0`, for a `ConfState` listing voters
`vs`, learners `ls`, outgoing voters `os`, staged learners `ns` and the auto-leave flag `al`: not
joint (no outgoing voter), one `Simple` per voter and learner (the staged learners as learners);
joint, one `Simple` adding each outgoing voter, then one `EnterJoint(al)` removing them and adding
the voters, learners and staged learners. (`toConfChangeSingle`, `chain`.) -/
def restore (m0 : Membership) (vs ls os ns : List w64) (al : Bool) : Option Membership :=
  let add := fun id => (⟨AddNode, id⟩ : Single)
  let addL := fun id => (⟨AddLearnerNode, id⟩ : Single)
  let rem := fun id => (⟨RemoveNode, id⟩ : Single)
  let inc := os.map rem ++ vs.map add ++ ls.map addL ++ ns.map addL
  if os = [] then simpleEach inc m0
  else (simpleEach (os.map add) m0).bind (enterJoint al inc)

/-- A `ConfState`'s lists list configuration `m` (each in any order, without repetition), with its
auto-leave flag (R1's `ConfState.Is`, over this batch's `Membership`). -/
def Lists (vs ls os ns : List w64) (al : Bool) (m : Membership) : Prop :=
  vs.Perm (elements m.voters) ∧ ls.Perm (elements m.learners) ∧
  os.Perm (elements m.votersOutgoing) ∧ ns.Perm (elements m.learnersNext) ∧ al = m.autoLeave

end ConfChange
end EtcdGrove
end Perennial
