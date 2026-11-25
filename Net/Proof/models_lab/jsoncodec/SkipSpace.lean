/-
The proof of `jsoncodec.SkipSpace` (`Net/Spec/models_lab/jsoncodec/SkipSpace.lean`): the loop,
over `IsSpace`'s spec. Ported from dsverify-lab's `wp_SkipSpace`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/GoBase.lean`, lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.SkipSpace
public import Net.Spec.models_lab.jsoncodec.IsSpace
public import Net.Proof.models_lab.jsoncodec.ScanString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem SkipSpace.wp_proof (wp_IsSpace : IsSpace.spec (GF := GF) (hG := hG)) :
    SkipSpace.spec (GF := GF) (hG := hG) := by
  intro b dq bs i hi
  unfold JsonScan.skipEnd
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  ihave IH : iprop(∃ (n : w64),
      "j" ∷ j_ptr ↦ n ∗
      "%Hn" ∷ ⌜uint.nat i ≤ uint.nat n ∧ uint.nat n ≤ bs.length ∧
        ∀ k < uint.nat n - uint.nat i, ∀ x, (bs.drop (uint.nat i))[k]? = some x →
          JsonScan.spB x = true⌝) $$ [j]
  · iexists _; iframe; ipureintro; refine ⟨Nat.le_refl _, hi, ?_⟩; intro k hk; omega
  wp_for IH
  wp_if_destruct
  · have Hlt : uint.nat n < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[uint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z b.len := by word
    have hnz : (sint.Z n).toNat = uint.nat n := by word
    rw [if_pos hb]
    wp_apply wp_load_slice_index b (sint.Z n) bs dq x hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [hnz]; exact Hx
    wp_apply (wp_IsSpace x)
    rw [spaceB_spB]
    by_cases hsp : JsonScan.spB x = true
    · simp only [hsp, decide_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k hk y hy
      by_cases hkn : k < uint.nat n - uint.nat i
      · exact Hn.2.2 k hkn y hy
      · have : k = uint.nat n - uint.nat i := by word
        subst this
        rw [List.getElem?_drop, show uint.nat i + (uint.nat n - uint.nat i) = uint.nat n by omega,
          Hx] at hy
        cases hy; exact hsp
    · simp only [Bool.not_eq_true] at hsp
      simp only [hsp]
      cleanup_bool_decide
      wp_auto
      have := takeWhile_len JsonScan.spB (bs.drop (uint.nat i)) (uint.nat n - uint.nat i) (by simp; omega)
        Hn.2.2 (Or.inr ⟨x, by rw [List.getElem?_drop,
          show uint.nat i + (uint.nat n - uint.nat i) = uint.nat n by omega]; exact Hx, hsp⟩)
      have e : W64 ((uint.nat i + ((List.drop (uint.nat i) bs).takeWhile JsonScan.spB).length : Nat) : Int) = n := by
        rw [this]; word
      rw [← e]; iapply HΦ; iframe
  · have hn : uint.nat n = bs.length := by word
    have := takeWhile_len JsonScan.spB (bs.drop (uint.nat i)) (uint.nat n - uint.nat i) (by simp; omega)
      Hn.2.2 (Or.inl (by simp; omega))
    have e : W64 ((uint.nat i + ((List.drop (uint.nat i) bs).takeWhile JsonScan.spB).length : Nat) : Int) = n := by
      rw [this]; word
    rw [← e]; iapply HΦ; iframe

end proof

end models_lab.jsoncodec
end Perennial
