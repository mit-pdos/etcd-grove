/-
`Changer.Simple` applies changes that alter the incoming config by at most one voter.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvConfchange
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `Simple(ccs...)`: `simpleM` on the tracker's state (`IsLearner` read from its
`Progress` values `pvs`); on success a fresh configuration and progress map, each
`Progress` a copy of the tracker's with only `IsLearner` changed or a fresh one
(`ownResult`). The tracker is only read. The `MaxInflight` bound is `NewInflights`'s
premise. (Generalized 2026-10-12 from `[AddNode id]` on a voters-only tracker; that case
is `Simple_votersOnly` in `Proof/.../confchange/Restore.lean`.) (2026-10-15, raft v3.7 retarget,
stage R2: `ccs` a slice of `*pb.ConfChangeSingle` pointers `ls`, each `ccsRO` of its change in
`l`; was a slice of the struct values `l`.) (raft#168: no `AddWitness` change, as for
`apply`; on a witness-free tracker, `ownTrackerCC`.) -/
abbrev confchange.Changer.Simple.spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (c : CfgM) (prs : GMap w64 Loc)
    (pvs : GMap w64 tracker.Progress) (ccs : GoSlice) (ls : List Loc) (l : List ConfChangeSingleM)
    (dq dqs dqc dqm dqp : DFrac),
  (0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗
      ([∗list] q;c ∈ ls;l, ccsRO q c) ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"Simple")) (Val #ccs))
  {{ (cfg : tracker.Config) (trk : Loc) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err);
      p ↦{dq} chg ∗ ccs ↦*{dqs} ls ∗ ownTrackerCC chg.Tracker' dqc dqm dqp c prs pvs ∗
      ownResult chg pvs (simpleM l { cfg := c, prs := flagsOf pvs }) cfg trk err }}

end spec

end EtcdGrove
end Perennial
