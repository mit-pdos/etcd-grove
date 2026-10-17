/-
`Changer.LeaveJoint` leaves a joint configuration. Lean-first (no Rocq counterpart);
see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `LeaveJoint()`: `leaveJointM` on the tracker's state. No `Progress` is allocated, so
no `MaxInflight` bound.

raft#168: an outgoing voter that is the incoming witness (`cfg.Witnesses[0] == id`) keeps
its `Progress`. On a witness-free configuration `Witnesses[0]` is `0`, which no id `apply`
adds is (it skips `NodeId == 0`): the premise `0 ∉ c.outgoing` makes the check false, and the
old statement holds. (Without it an outgoing voter `0` would now be kept: the one place the
witness-free behaviour differs, unreachable through `confchange`.) -/
abbrev confchange.Changer.LeaveJoint.spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (c : CfgM) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (dq dqc dqm dqp : DFrac),
  W64 0 ∉ c.outgoing →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"LeaveJoint")) (Val #()))
  {{ (cfg : tracker.Config) (trk : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err);
      p ↦{dq} chg ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs ∗
      ownResult chg pvs (leaveJointM { cfg := c, prs := flagsOf pvs }) cfg trk err }}

end spec

end EtcdGrove
end Perennial
