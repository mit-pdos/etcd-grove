/-
The proof of `Net/Spec/models_lab/pbcodec/SizeVarint.lean`: the loop keeps
`varintSize v = n - 1 + varintSize x` (each iteration drops seven bits of `x`).
-/
module

public import Net.Spec.models_lab.pbcodec.SizeVarint

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

theorem SizeVarint.wp_proof : SizeVarint.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start
  wp_auto
  ihave HI : (∃ (n x : w64), "n" ∷ n_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x ∗
      "%Hn" ∷ ⌜1 ≤ uint.nat n ∧ uint.nat n ≤ 10 ∧
        EtcdGrove.varintSize (uint.nat v) = uint.nat n - 1 + EtcdGrove.varintSize (uint.nat x)⌝ :
      IProp GF) $$ [n x]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by word⟩
  wp_for HI
  by_cases Hlt : uint.Z (W64 128) ≤ uint.Z x
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hx : ¬ uint.nat x < 128 := by word
    have hs := varintSize_w64_ge x hx
    have h10 := varintSize_le (uint.nat v) (by word)
    have h1 : 1 ≤ EtcdGrove.varintSize (uint.nat (x >>> W64 7)) := by
      unfold EtcdGrove.varintSize; rw [EtcdGrove.varintEnc]; split <;> simp
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    have : uint.nat (n + W64 1) = uint.nat n + 1 := by word
    rw [this, Hn.2.2, hs]; omega
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    have hx : uint.nat x < 128 := by word
    rw [varintSize_w64_lt x hx] at Hn
    have he : (W64 (EtcdGrove.varintSize (uint.nat v) : Nat) : w64) = n := by
      rw [Hn.2.2]; word
    rw [he]
    iapply HΦ
    itrivial

end proof

end models_lab.pbcodec
end Perennial
