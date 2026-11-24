/-
The proof of `skipSpace` (`Spec/encoding/json/Codec/skipSpace.lean`): the loop's index `i` stays
within the slice, every byte before it whitespace; it stops at the slice's end or at a byte that is
not whitespace, so at `leadSpace bs`.
-/
module

public import Spec.encoding.json.Codec.skipSpace
public import Spec.encoding.json.Codec.isSpace

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- `leadSpace bs` is the `n` before which every byte is whitespace and at which one is not, or
the end. -/
theorem leadSpace_eq (bs : List w8) (n : Nat) (hn : n ≤ bs.length)
    (hall : ∀ k < n, ∀ x, bs[k]? = some x → isSpaceB x = true)
    (hstop : ∀ x, bs[n]? = some x → isSpaceB x = false) : leadSpace bs = n := by
  induction bs generalizing n with
  | nil => simp at hn; subst hn; rfl
  | cons c t ih =>
    cases n with
    | zero =>
      have hc := hstop c rfl
      simp [leadSpace, hc]
    | succ m =>
      have hc := hall 0 (Nat.succ_pos m) c rfl
      have := ih m (by simp at hn; omega)
        (fun k hk x hx => hall (k + 1) (by omega) x (by simpa using hx))
        (fun x hx => hstop x (by simpa using hx))
      simp only [leadSpace, List.takeWhile_cons, hc, ↓reduceIte, List.length_cons] at this ⊢
      omega

/-- The loop's step: `i + 1` stays within `[0, n]`, one more than `i`. -/
theorem skip_step (i n : w64) (h1 : 0 ≤ sint.Z i) (h2 : sint.Z i < sint.Z n) :
    0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z n ∧
      sint.nat (i + W64 1) = sint.nat i + 1 := by
  have h3 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
  rw [h3]
  refine ⟨Int.le_trans h1 (Int.le_add_of_nonneg_right (by decide)), Int.add_one_le_of_lt h2, ?_⟩
  simp only [sint.nat, h3]; exact Int.toNat_add_nat h1 1

theorem skipSpace.wp_proof (wp_isSpace : isSpace.spec (GF := GF) (hG := hG)) :
    skipSpace.spec (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hs
  wp_auto
  ihave %Hs_len := ownSlice_len _ _ _ $$ Hs
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b.len ∧
        ∀ k < sint.nat i, ∀ x, bs[k]? = some x → isSpaceB x = true⌝ : IProp GF) $$ [i]
  · iexists (W64 0)
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro k hk; simp [sint.nat] at hk
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z i < sint.Z b.len := by simpa using Hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif'⟩)]
    have hlt : (sint.Z i).toNat < bs.length := by
      rw [Hs_len.1]; exact (Int.toNat_lt_toNat (Int.lt_of_le_of_lt Hi.1 Hif')).2 Hif'
    obtain ⟨x, Hx⟩ : ∃ x, bs[(sint.Z i).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
    wp_apply wp_load_slice_index _ _ _ _ x Hi.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx
    wp_apply wp_isSpace x
    cases hsp : isSpaceB x
    · simp only [intoVal_eq_iff, Bool.false_eq_true, decide_False_any, decide_True_any, ↓reduceIte]
      wp_auto
      have hlead : leadSpace bs = sint.nat i := by
        apply leadSpace_eq
        · simp only [sint.nat, sint.Z] at Hs_len Hi Hif' ⊢; omega
        · exact Hi.2.2
        · intro y hy
          have hy' : bs[(sint.Z i).toNat]? = some y := hy
          rw [Hx] at hy'
          cases hy'
          exact hsp
      have hW : W64 ↑(leadSpace bs) = i := by
        rw [hlead]; simp only [sint.nat, sint.Z] at Hi ⊢; word
      rw [hW]
      iapply HΦ $$ Hs
    · simp only [decide_True_any, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      obtain ⟨hb1, hb2, e⟩ := skip_step i b.len Hi.1 Hif'
      have hb := And.intro hb1 hb2
      iexists (i + W64 1)
      iframe
      ipureintro
      refine ⟨hb.1, hb.2, ?_⟩
      intro k hk y hy
      rw [e] at hk
      by_cases hkn : k < sint.nat i
      · exact Hi.2.2 k hkn y hy
      · have hkeq : k = sint.nat i := by omega
        rw [hkeq] at hy
        have hy' : bs[(sint.Z i).toNat]? = some y := hy
        rw [Hx] at hy'
        cases hy'
        exact hsp
  · have hie : sint.nat i = bs.length := by
      simp only [sint.nat, sint.Z] at Hs_len Hi Hif ⊢; omega
    have hlead : leadSpace bs = sint.nat i := by
      apply leadSpace_eq
      · omega
      · exact Hi.2.2
      · intro y hy; rw [hie] at hy; simp at hy
    have hW : W64 ↑(leadSpace bs) = i := by
      rw [hlead]; simp only [sint.nat, sint.Z] at Hi ⊢; word
    rw [hW]
    iapply HΦ $$ Hs

end proof

end encoding.json
end Perennial
