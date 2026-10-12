/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.newNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem newNode.wp_proof : newNode.spec (GF := GF) (hG := hG) := by
  intro rn
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := msgWithResult) as %c0 %γ0 ⟨#H0, %_, O0⟩
  wp_apply chan.wp_make1 (V := raftpb.Message) as %c1 %γ1 ⟨#H1, %_, O1⟩
  wp_apply chan.wp_make1 (V := raftpb.ConfChangeV2) as %c2 %γ2 ⟨#H2, %_, O2⟩
  wp_apply chan.wp_make1 (V := raftpb.ConfState) as %c3 %γ3 ⟨#H3, %_, -⟩
  wp_apply chan.wp_make1 (V := Ready) as %c4 %γ4 ⟨#H4, %_, O4⟩
  wp_apply chan.wp_make1 (V := Unit) as %c5 %γ5 ⟨#H5, %_, O5⟩
  wp_apply chan.wp_make2 (V := Unit) (W64 128) as %c6 %γ6 ⟨#H6, %_, O6⟩
  · ipureintro; decide
  wp_apply chan.wp_make1 (V := Unit) as %c7 %γ7 ⟨#H7, %_, O7⟩
  wp_apply chan.wp_make1 (V := Unit) as %c8 %γ8 ⟨#H8, %_, O8⟩
  wp_apply chan.wp_make1 (V := GoChan) as %c9 %γ9 ⟨#H9, %_, O9⟩
  ihave O6 : ownChan γ6 Unit (.Buffered []) $$ O6
  iapply HΦ
  isplitr
  · ipureintro; rfl
  unfold newNodeChans
  iexists γ0, γ1, γ2, γ4, γ5, γ6, γ7, γ8, γ9
  simp only
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
