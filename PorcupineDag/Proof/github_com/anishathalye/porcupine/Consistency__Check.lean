/- Lean-first (no Rocq counterpart).

`(*Consistency).Check(a, b)`: the loop over `[RealTime, GeneralLikely]` (`Oracles.lean`).
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.Consistency__Check
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Oracles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem Consistency.Check.wp_proof : Consistency.Check.spec (GF := GF) (hG := hG) :=
    fun cp c dqc pa pb a b dqa dqb => by
  wp_start as ⟨Hc, #Hlin, Ha, Hb⟩
  iunfold isLinearizability at Hlin
  icases Hlin with ⟨#Hor, %Hval⟩
  icases typedPointsto_not_null_dup cp c dqc $$ Hc with ⟨Hc, %Hnc⟩
  icases typedPointsto_not_null_dup pa a dqa $$ Ha with ⟨Ha, %Hna⟩
  icases typedPointsto_not_null_dup pb b dqb $$ Hb with ⟨Hb, %Hnb⟩
  iStructNamedSuffix Hc "c"
  iStructNamedSuffix Ha "a"
  iStructNamedSuffix Hb "b"
  simp only [DontKnow, HardBefore, HardAfter, SoftBefore, SoftAfter, Concurrent]
  ihave %Hlen := ownSlice_len $$ Hor
  wp_auto
  ihave HI : (∃ (i okv : w64) (f : GoFunc),
      "i" ∷ i_ptr ↦ i ∗ "ok" ∷ ok_ptr ↦ okv ∗ "o" ∷ o_ptr ↦ f ∗
      "%Hi" ∷ ⌜(sint.Z i = 0 ∧ okv = W64 0) ∨ (sint.Z i = 1 ∧ okv = rtOrder a.Op' b.Op') ∨
        (sint.Z i = 2 ∧ okv = linOrder a.Op' b.Op')⌝ : IProp GF) $$ [i ok o]
  · iexists W64 0, W64 0, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z c.Oracles'.len := by
      refine ⟨by omega, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    rcases Hi with ⟨Hi0, rfl⟩ | ⟨Hi1, rfl⟩ | ⟨Hi2, -⟩
    · wp_apply wp_load_slice_index c.Oracles' (sint.Z i) [rtV, glV] DFrac.discard rtV Hb.1 $$ [] as -
      · isplit
        · iexact Hor
        · ipureintro; simp [Hi0]
      wp_apply wp_rtV $$ [$Opa $Opb] as ⟨Opa, Opb⟩
      repeat' wp_if_destruct
      all_goals first
        | (exfalso; rcases rtOrder_cases a.Op' b.Op' with h | h | h <;> simp only [h] at * <;>
            contradiction)
        | (wp_for_post; iframe; iexists _, _, _; iframe; ipureintro; right; left
           exact ⟨by word, by simp only [*]⟩)
    · wp_apply wp_load_slice_index c.Oracles' (sint.Z i) [rtV, glV] DFrac.discard glV Hb.1 $$ [] as -
      · isplit
        · iexact Hor
        · ipureintro; simp [Hi1]
      wp_apply wp_glV $$ [$Opa $Opb] as ⟨Opa, Opb⟩
      repeat' wp_if_destruct
      all_goals first
        | (exfalso; rcases glOrder_cases a.Op' b.Op' with h | h | h <;> simp only [h] at * <;>
            contradiction)
        | (wp_for_post; iframe; iexists _, _, _; iframe; ipureintro; right; right
           refine ⟨by word, ?_⟩)
      all_goals
        rw [linOrder_eq]
        rcases rtOrder_cases a.Op' b.Op' with h | h | h <;>
          rcases glOrder_cases a.Op' b.Op' with g | g | g <;> simp only [h, g] at * <;>
          (try split) <;> word
    · exfalso; have := Hlen.1; simp only [List.length_cons, List.length_nil] at this; word
  · have Hi2 : okv = linOrder a.Op' b.Op' := by
      have := Hlen.1; simp only [List.length_cons, List.length_nil] at this
      rcases Hi with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, h⟩
      · exfalso; word
      · exfalso; word
      · exact h
    subst Hi2
    iapply HΦ
    isplitl [Oraclesc Validc]
    · iapply typedPointsto_combine cp c dqc Hnc
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitl [Opa globalIda ida firstUnka visiteda]
    · iapply typedPointsto_combine pa a dqa Hna
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · iapply typedPointsto_combine pb b dqb Hnb
      simp only [TypedPointsto.typedPointstoDef]
      iframe

end proof

end porcupine
end EtcdGrove
end Perennial
