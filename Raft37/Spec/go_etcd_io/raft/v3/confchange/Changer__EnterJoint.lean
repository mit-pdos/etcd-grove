/-
`Changer.EnterJoint` enters a joint configuration: the outgoing config a copy of the
incoming one, then the changes. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvConfchange
public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `EnterJoint(autoLeave, ccs...)`: `enterJointM` on the tracker's state. (2026-10-15, raft v3.7
retarget, stage R2: `ccs` a slice of `*pb.ConfChangeSingle` pointers `ls`, each `ccsRO` of its
change in `l`; was a slice of the struct values `l`.) -/
abbrev confchange.Changer.EnterJoint.spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (c : CfgM) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (autoLeave : Bool) (ccs : GoSlice) (ls : List Loc)
    (l : List ConfChangeSingleM) (dq dqs dqc dqm dqp : DFrac),
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗
      ([∗list] q;c ∈ ls;l, ccsRO q c) ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs }}
    (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"EnterJoint")) (Val #autoLeave)) (Val #ccs))
  {{ (cfg : tracker.Config) (trk : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err);
      p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs ∗
      ownResult chg pvs (enterJointM autoLeave l { cfg := c, prs := flagsOf pvs }) cfg trk err }}

end spec

end EtcdGrove
end Perennial
