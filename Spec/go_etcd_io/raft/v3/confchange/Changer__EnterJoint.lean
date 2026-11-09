/-
## `Changer.EnterJoint(autoLeave, ccs...)`

**Users.** `raft.applyConfChange` (`raft.go:1961`: a joint transition, or several changes), `Restore`
(`restore.go:156`, a joint `ConfState`); the examples' pre-check. Snippets `raftconf/confchange.go`
(`ReqJointCycle`, `ReqApplyLikeRaft`).

**Proof sketch.** `checkAndCopy`; `joint`; the incoming half's `len`; the outgoing half a fresh
map (`outgoingPtr`), filled by `range` over the incoming one; `apply`; `AutoLeave` stored;
`checkAndReturn`; `ccState_done` (valid: `transitions_valid`) or `ccState_abort`.

**Changes** (from `specs-ref`'s `confchange/Changer__EnterJoint.lean`): as `Simple`'s.

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

/-- `EnterJoint(autoLeave, cs...)`: `changed B (enterJoint autoLeave cs m)`. -/
def Changer.EnterJoint.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (chg : go_etcd_io.raft.v3.confchange.Changer) (dqc : DFrac)
    (m : Membership) (B : Base) (autoLeave : Bool) (sl : GoSlice) (dqs : DFrac) (cs : List Single),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dqp} chg ∗
      configOwn chg.Tracker'.Config' dqc m ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m B.pv⌝ ∗ ccsPts sl dqs cs }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.confchange.Changer.ty @!! go!"EnterJoint")) (Val #autoLeave)) (Val #sl))
  {{ (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err);
      p ↦{dqp} chg ∗ configOwn chg.Tracker'.Config' dqc m ∗ ccsPts sl dqs cs ∗ changed B (enterJoint autoLeave cs m) cfg trk err }}

end spec
end ConfChange
end EtcdGrove
end Perennial
