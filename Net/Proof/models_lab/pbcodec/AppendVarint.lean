/-
The proof of `Net/Spec/models_lab/pbcodec/AppendVarint.lean`: the loop keeps
`varintEnc v = pre ++ varintEnc x`, `out` holding `bs ++ pre` (each iteration appends the low seven
bits of `x` with the continuation bit and drops them).
-/
module

public import Net.Spec.models_lab.pbcodec.AppendVarint

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.pbcodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.pbcodec.Assumptions]

set_option goose.wp.extras true

theorem AppendVarint.wp_proof : AppendVarint.spec (GF := GF) (hG := hG) := by
  intro b bs v
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave HI : (∃ (o : GoSlice) (pre : List w8) (x : w64), "out" ∷ out_ptr ↦ o ∗ "x" ∷ x_ptr ↦ x ∗
      "Ho" ∷ o ↦* (bs ++ pre) ∗ "Hcap" ∷ ownSliceCap w8 o (DFrac.own 1) ∗
      "%Hx" ∷ ⌜EtcdGrove.varintEnc (uint.nat v) = pre ++ EtcdGrove.varintEnc (uint.nat x)⌝ :
      IProp GF) $$ [out x Hb Hcap]
  · iexists _, [], _
    simp only [List.append_nil]
    iframe
    ipureintro; simp
  wp_for HI
  by_cases Hlt : uint.Z (W64 128) ≤ uint.Z x
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    (try wp_auto)
    have hx : ¬ uint.nat x < 128 := by word
    rw [lowByte]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, Hocap⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Ho $Hcap $Hosl] as %o' ⟨Ho', Hcap', -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists o', pre ++ [W8 (uint.nat x % 128 + 128)], _
    simp only [List.append_assoc]
    iframe
    ipureintro
    rw [Hx, varintEnc_w64_ge x hx]
    simp
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    have hx : uint.nat x < 128 := by word
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, Hocap⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Ho $Hcap $Hosl] as %o' ⟨Ho', Hcap', -⟩
    (try wp_auto)
    iapply HΦ
    rw [Hx, varintEnc_w64_lt x hx]
    have hz : (W8 (uint.Z x) : w8) = W8 (uint.nat x : Int) := by
      congr 1
    rw [hz, List.append_assoc]
    iframe

end proof

end models_lab.pbcodec
end Perennial
