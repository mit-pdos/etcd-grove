/-
Proof of `Spec/WithSort.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithSort
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

theorem WithSort.wp_proof : WithSort.spec (GF := GF) (hG := hG) := by
  intro target order
  wp_start as %Hns
  iapply wp_fupd
  wp_auto
  ipersist target
  ipersist order
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold optSpec
  imodintro
  iintro %opp %op %o
  wp_start as ⟨Hop, #Hat⟩
  iapply wp_fupd
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · exfalso; simp_all
    ipersist «$r0»
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    imodintro
    iapply HΦ
    iframe Hop
    unfold opFullAt opAt OpFields
    icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht, #Hv, #Hs⟩
    simp only [withSortM]
    iframe #
    isplitl []
    · ipureintro; simp_all
    isplitl []
    · ipureintro; simp_all
    unfold opSortAt
    simp only [↓reduceIte]
    rw [if_neg (show ¬ (True ∧ order = W64 1) by simpa using Hns)]
    iexact «$r0»
  · ipersist «$r0»
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    imodintro
    iapply HΦ
    iframe Hop
    unfold opFullAt opAt OpFields
    icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht, #Hv, #Hs⟩
    simp only [withSortM]
    iframe #
    isplitl []
    · ipureintro; simp_all
    isplitl []
    · ipureintro; simp_all
    unfold opSortAt
    simp only [↓reduceIte, if_neg Hns]
    iexact «$r0»

end proof

end EtcdGrove
end Perennial
