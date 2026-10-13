/-
Proof of `Spec/go_etcd_io/raft/v3/confChangeToMsg.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confChangeToMsg
public import Spec.go_etcd_io.raft.v3.raftpb.MarshalConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confChangeToMsg.wp_proof
    (wp_raftpb_MarshalConfChange : raftpb.MarshalConfChange.spec (GF := GF) (hG := hG)) :
    confChangeToMsg.spec (GF := GF) (hG := hG) := by
  intro c o dq
  wp_start as Hc
  wp_auto
  wp_apply wp_raftpb_MarshalConfChange $$ [$Hc] as %data %bs ⟨Hc, Hdata, %Hbs⟩
  wp_apply wp_slice_literal (V := raftpb.Entry) [ccEntry o data]
  isplitr
  · ipureintro; rfl
  iintro %ents ⟨Hents, -⟩
  simp only [raftpb.MsgProp]
  wp_auto
  simp only [ccPropMsg]
  iapply HΦ
  iframe
  ipureintro; exact Hbs

end proof

end EtcdGrove
end Perennial
