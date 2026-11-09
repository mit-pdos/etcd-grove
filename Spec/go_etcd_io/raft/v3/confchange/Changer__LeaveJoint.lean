/-
## `Changer.LeaveJoint()`

**Users.** `raft.applyConfChange` (`raft.go:1959`: the zero `ConfChangeV2`, which raft proposes
itself on auto-leave, `raft.go:742`); the examples' pre-check. Snippet `raftconf/confchange.go`
(`ReqJointCycle`).

**Proof sketch.** `checkAndCopy`; `joint`; the staged learners into `Learners` (`nilAwareAdd`) and
marked (`trk[id].IsLearner = true`: tracked, by `ccState`); `LearnersNext = nil`; the outgoing
voters that are neither incoming voters nor learners untracked; the outgoing half `nil`;
`AutoLeave = false`; `checkAndReturn`; `ccState_done` or `ccState_abort`.

**Changes** (from `specs-ref`'s `confchange/Changer__LeaveJoint.lean`): as `Simple`'s.

**Margin.** As `Simple`'s.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- `LeaveJoint()`: `changed B (leaveJoint m)`. -/
def Changer.LeaveJoint.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (dqc : DFrac)
    (m : Membership) (B : Base),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗
      configOwn chg.Tracker'.Config' dqc m ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m B.pv⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"LeaveJoint")) (Val #()))
  {{ (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err);
      p ↦{dqp} chg ∗ configOwn chg.Tracker'.Config' dqc m ∗ changed B (leaveJoint m) cfg trk err }}

end spec
end ConfChange
end EtcdGrove
end Perennial
