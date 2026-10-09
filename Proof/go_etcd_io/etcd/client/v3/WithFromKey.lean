/-
Proof of `Spec/WithFromKey.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithFromKey

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

theorem WithFromKey.wp_proof : WithFromKey.spec (GF := GF) (hG := hG) := by
  wp_start
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold optSpec
  imodintro
  iintro %opp %op %o
  wp_start as ⟨Hop, #Hat⟩
  iapply wp_fupd
  unfold opFullAt opAt OpFields
  icases Hat with ⟨⟨%Hf, #He⟩, #Hk, %Ht⟩
  ihave %Hklen := ownSlice_len _ _ _ $$ Hk
  wp_auto
  wp_if_destruct
  · have Hk0 : o.key = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hklen.1, Hif]; rfl
    wp_apply wp_slice_literal (l := [W8 0])
    isplitr
    · ipureintro; rfl
    iintro %ksl ⟨Hks, -⟩
    wp_auto
    wp_apply wp_string_to_bytes _ as %esl ⟨Hes, -⟩
    ipersist Hks
    ipersist Hes
    imodintro
    iapply HΦ
    iframe Hop
    simp only [withFromKeyM, Hk0, ↓reduceIte]
    isplitl []
    · isplitl []
      · ipureintro; exact Hf
      · rw [show ([W8 0] : List w8) = [0#8] from rfl]; iexact Hes
    isplitl []
    · rw [show ([W8 0] : List w8) = [0#8] from rfl]; iexact Hks
    ipureintro; exact ⟨Ht.1, Ht.2.1, Ht.2.2.1, trivial, Ht.2.2.2.2⟩
  · have Hk0 : o.key ≠ [] := by
      intro h; apply Hif; rw [h] at Hklen; simp at Hklen; word
    wp_apply wp_string_to_bytes _ as %esl ⟨Hes, -⟩
    ipersist Hes
    imodintro
    iapply HΦ
    iframe Hop
    simp only [withFromKeyM, Hk0, ↓reduceIte]
    isplitl []
    · isplitl []
      · ipureintro; exact Hf
      · rw [show ([W8 0] : List w8) = [0#8] from rfl]; iexact Hes
    isplitl []
    · iexact Hk
    ipureintro; exact ⟨Ht.1, Ht.2.1, Ht.2.2.1, trivial, Ht.2.2.2.2⟩

end proof

end EtcdGrove
end Perennial
