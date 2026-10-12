/-
Proof of `Spec/WithRange.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem WithRange.wp_proof : WithRange.spec (GF := GF) (hG := hG) := by
  intro endKey
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist endKey
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold optSpec
  imodintro
  iintro %opp %op %o
  wp_start as ⟨Hop, #Hat⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_string_to_bytes endKey as %sl ⟨Hsl, -⟩
  ipersist Hsl
  imodintro
  iapply HΦ
  iframe
  unfold opFullAt opAt OpFields
  icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht, #Hv, #Hs⟩
  simp only [withRangeM]
  iframe #
  isplitl []
  · ipureintro; simp_all
  isplitl []
  · ipureintro; simp_all
  · iapply opSortAt_of _ o _ (by simp) (by simp) (by simp) $$ Hs

end proof

end EtcdGrove
end Perennial
