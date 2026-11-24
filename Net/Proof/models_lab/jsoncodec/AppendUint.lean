/-
The proof of `jsoncodec.AppendUint` (`Net/Spec/models_lab/jsoncodec/AppendUint.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendUint


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem AppendUint.wp_proof : AppendUint.spec (GF := GF) (hG := hG) := by
  intro b bs x
  induction h : x.toNat using Nat.strongRecOn generalizing b bs x with
  | _ n ih =>
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · have hlt : (x / W64 10).toNat < n := by
      rw [← h, BitVec.toNat_udiv]; have : (W64 10 : w64).toNat = 10 := rfl
      rw [this]; have : 10 ≤ x.toNat := by simp only [uint.Z] at Hif; omega
      omega
    wp_apply (ih _ hlt b bs (x / W64 10) rfl) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    wp_apply wp_slice_literal (V := w8)
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b2 ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe Hcap
    iapply (slice_pts_eq _ _ _ ?_) $$ Hb
    rw [decU64_step x (by have e : (W64 10 : w64).toNat = 10 := rfl; simp only [uint.Z] at Hif; omega), List.append_assoc]
  · wp_apply wp_slice_literal (V := w8)
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b2 ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe Hcap
    iapply (slice_pts_eq _ _ _ ?_) $$ Hb
    rw [decU64_small x (by have e : (W64 10 : w64).toNat = 10 := rfl; simp only [uint.Z] at Hif; omega)]

end proof

end models_lab.jsoncodec
end Perennial
