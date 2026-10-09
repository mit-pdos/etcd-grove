/-
Proof of `Spec/KeyPredForRange.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.KeyPredForRange
public import Spec.go_etcd_io.etcd.cache.v3.ExactKey
public import Spec.go_etcd_io.etcd.cache.v3.FromKey
public import Spec.go_etcd_io.etcd.cache.v3.Range

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem KeyPredForRange.wp_proof
    (wp_ExactKey : ExactKey.spec (GF := GF) (hG := hG))
    (wp_FromKey : FromKey.spec (GF := GF) (hG := hG))
    (wp_Range : Range.spec (GF := GF) (hG := hG)) :
    KeyPredForRange.spec (GF := GF) (hG := hG) := by
  intro startSl endSl start end_
  wp_start as ⟨#Hstart, #Hend⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hend
  wp_auto
  wp_if_destruct
  · have he : end_ = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1, Hif]; rfl)
    wp_apply wp_ExactKey $$ [$Hstart] as %f Hf
    simp only [keyPredForRange, he, ↓reduceIte]
    iapply HΦ $$ Hf
  · have hne : end_ ≠ [] := by
      intro he; subst he; apply Hif; simp at Hlen; word
    wp_if_destruct
    · have hl1 : end_.length = 1 := by rw [Hlen.1, Hif]; rfl
      obtain ⟨c, rfl⟩ : ∃ c, end_ = [c] := by
        match end_, hl1 with
        | [c], _ => exact ⟨c, rfl⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z endSl.len by
        rw [Hif]; decide))]
      wp_apply wp_load_slice_index endSl (sint.Z (W64 0)) [c] _ c (by decide) $$ [Hend] as -
      · iframe Hend; ipureintro; rfl
      wp_if_destruct
      · wp_apply wp_FromKey $$ [$Hstart] as %f Hf
        simp only [keyPredForRange, List.cons_ne_nil, ↓reduceIte]
        iapply HΦ $$ Hf
      · wp_apply wp_Range startSl endSl start [c] $$ [$Hstart $Hend] as %f Hf
        have hc : [c] ≠ [W8 0] := by intro h; cases h; exact Hif rfl
        simp only [keyPredForRange, List.cons_ne_nil, hc, ↓reduceIte]
        iapply HΦ $$ Hf
    · wp_apply wp_Range startSl endSl start end_ $$ [$Hstart $Hend] as %f Hf
      have hc : end_ ≠ [W8 0] := by intro h; subst h; apply Hif; simp at Hlen; word
      simp only [keyPredForRange, hne, hc, ↓reduceIte]
      iapply HΦ $$ Hf

end proof

end EtcdGrove
end Perennial
