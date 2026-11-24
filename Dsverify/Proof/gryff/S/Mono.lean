/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/S/Mono.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit S: the three `crtInstance` lower-bound authorities (`epaxosOwn`'s `[∗list] q ∈ finRange 3,
monoNatAuthOwn (ρ.crt q) 1 _`): a lower bound out, a lower bound below.
-/
module

public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff.unitS

open Iris Iris.BI ProofMode Perennial

variable {GF : BundledGFunctors} [AllG GF]

theorem finRange3 : List.finRange 3 = [0, 1, 2] := by decide

theorem fin3_cases (q : Fin 3) : q = 0 ∨ q = 1 ∨ q = 2 := by revert q; decide

/-- A lower bound of row `q`'s authority. -/
theorem monos_lb (f : Fin 3 → GName) (g : Fin 3 → Nat) (q : Fin 3) :
    ([∗list] q' ∈ List.finRange 3, (monoNatAuthOwn (f q') 1 (g q') : IProp GF)) ⊢
      ([∗list] q' ∈ List.finRange 3, monoNatAuthOwn (f q') 1 (g q')) ∗
        monoNatLbOwn (f q) (g q) := by
  rw [finRange3]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
  ihave #L0 := monoNatLbOwn_get (f 0) 1 (g 0) $$ H0
  ihave #L1 := monoNatLbOwn_get (f 1) 1 (g 1) $$ H1
  ihave #L2 := monoNatLbOwn_get (f 2) 1 (g 2) $$ H2
  isplitl
  · iapply BigSepL.bigSepL_cons.2; iframe H0
    iapply BigSepL.bigSepL_cons.2; iframe H1
    iapply BigSepL.bigSepL_cons.2; iframe H2
    iapply BigSepL.bigSepL_nil.2
    itrivial
  · rcases fin3_cases q with rfl | rfl | rfl
    · iexact L0
    · iexact L1
    · iexact L2

/-- One authority with a lower bound: the bound is below (the authority kept). -/
theorem auth_lb_le (γ : GName) (q : Qp) (a n : Nat) :
    (monoNatAuthOwn γ q a : IProp GF) ∗ monoNatLbOwn γ n ⊢ monoNatAuthOwn γ q a ∗ ⌜n ≤ a⌝ := by
  refine (persistent_entails_left (Q := iprop(⌜n ≤ a⌝)) ?_).trans ?_
  · iintro ⟨H, Hlb⟩
    icases monoNatLbOwn_valid γ q a n $$ H Hlb with %⟨-, h⟩
    ipureintro; exact h
  · iintro ⟨⟨H, -⟩, %h⟩
    iframe H; ipureintro; exact h

/-- A lower bound of row `q` is below its authority. -/
theorem monos_le (f : Fin 3 → GName) (g : Fin 3 → Nat) (q : Fin 3) (n : Nat) :
    ([∗list] q' ∈ List.finRange 3, (monoNatAuthOwn (f q') 1 (g q') : IProp GF)) ∗
        monoNatLbOwn (f q) n ⊢
      ([∗list] q' ∈ List.finRange 3, monoNatAuthOwn (f q') 1 (g q')) ∗ ⌜n ≤ g q⌝ := by
  rw [finRange3]
  iintro ⟨H, Hlb⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, -⟩
  rcases fin3_cases q with rfl | rfl | rfl
  · icases auth_lb_le (f 0) 1 (g 0) n $$ [H0 Hlb] with ⟨H0, %h⟩
    · iframe
    isplitl
    · iapply BigSepL.bigSepL_cons.2; iframe H0
      iapply BigSepL.bigSepL_cons.2; iframe H1
      iapply BigSepL.bigSepL_cons.2; iframe H2
      iapply BigSepL.bigSepL_nil.2; itrivial
    · ipureintro; exact h
  · icases auth_lb_le (f 1) 1 (g 1) n $$ [H1 Hlb] with ⟨H1, %h⟩
    · iframe
    isplitl
    · iapply BigSepL.bigSepL_cons.2; iframe H0
      iapply BigSepL.bigSepL_cons.2; iframe H1
      iapply BigSepL.bigSepL_cons.2; iframe H2
      iapply BigSepL.bigSepL_nil.2; itrivial
    · ipureintro; exact h
  · icases auth_lb_le (f 2) 1 (g 2) n $$ [H2 Hlb] with ⟨H2, %h⟩
    · iframe
    isplitl
    · iapply BigSepL.bigSepL_cons.2; iframe H0
      iapply BigSepL.bigSepL_cons.2; iframe H1
      iapply BigSepL.bigSepL_cons.2; iframe H2
      iapply BigSepL.bigSepL_nil.2; itrivial
    · ipureintro; exact h

/-- A wand from a pure premise into a persistent (absorbing) proposition is persistent
(`icoordOk`'s callbacks: `⌜..⌝ -∗ specT ..`). -/
theorem pureWand_persistent {PROP : Type _} [BI PROP] [BIPersistentlyForall PROP] (φ : Prop) (P : PROP) [Persistent P]
    [Absorbing P] : Persistent iprop(⌜φ⌝ -∗ P) :=
  ⟨pure_wand_forall.1.trans <| Persistent.persistent.trans (persistently_mono pure_wand_forall.2)⟩

end Perennial.gryff.unitS
