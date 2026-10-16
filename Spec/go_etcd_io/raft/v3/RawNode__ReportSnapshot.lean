/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A snapshot sent to `to` succeeded or failed (`MsgSnapStatus`, local): a `Progress` state only.
(raft#243: a third argument, the follower's applied snapshot index `asi`. The statement is
unchanged, for every `asi`, but it is false of the PR's code for an `asi` other than `0` or the
peer's acknowledged `Match`: the success arm of `stepLeader`'s `MsgSnapStatus` sets `Match` to
it, and is a `sorry` there, `stepLeader/Rest.lean`. See notes/pr-verify/raft-243.md.) -/
abbrev RawNode.ReportSnapshot.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (to : w64) (st : SnapshotStatus)
    (asi : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (App (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReportSnapshot")) (Val #to)) (Val #st)) (Val #asi))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs }}

end spec

end EtcdGrove
end Perennial
