/- Lean-first (no Rocq counterpart). The proof of `watchCheck.expect`: the outer loop over the
revisions `r` from the watcher's; before `r`, nothing returned, so `expNext`'s answer is the head of
what is left (`expRem`: `r`'s in-range changes past the skipped ones, then the later revisions'); the
inner loop over `r`'s changes, after `j` of them, has seen `seen` in-range ones, all skipped (at most
the skip: the watcher's index at its revision, `0` past it). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__changesAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.inRange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem watchCheck.expect.wp_proof (wp_changesAt : history.changesAt.spec (GF := GF) (hG := hG))
    (wp_inRange : inRange.spec (GF := GF) (hG := hG)) :
    watchCheck.expect.spec (GF := GF) (hG := hG) := by
  intro c h γ Hlb w wv kk e upto dq dqw dqk dqe hrev0 hidx0 hupto hupto'
  wp_start as ⟨Hh, Hw, Hk, He, Hrd, #Hlb⟩
  icases (typedPointsto_not_null_dup _ _ _) $$ Hw with ⟨Hw, %Hwn⟩
  iStructNamedSuffix Hw "W"
  wp_auto
  ihave IH : (∃ (r : w64),
      "r" ∷ r_ptr ↦ r ∗ "Hh" ∷ c.[watchCheck, go!"h"] ↦{dq} h ∗ "Hrd" ∷ histRd h γ ∗
      "keyW" ∷ w.[watcher, go!"key"] ↦{dqw} wv.key' ∗
      "end'W" ∷ w.[watcher, go!"end"] ↦{dqw} wv.end' ∗
      "revW" ∷ w.[watcher, go!"rev"] ↦{dqw} wv.rev' ∗
      "indexW" ∷ w.[watcher, go!"index"] ↦{dqw} wv.index' ∗
      "Hk" ∷ wv.key' ↦*{dqk} kk ∗ "He" ∷ wv.end' ↦*{dqe} e ∗
      "c" ∷ c_ptr ↦ c ∗ "upto" ∷ upto_ptr ↦ upto ∗ "w" ∷ w_ptr ↦ w ∗
      "%Hr" ∷ ⌜sint.Z wv.rev' ≤ sint.Z r ∧ (sint.Z r ≤ sint.Z upto + 1 ∨ r = wv.rev') ∧
        expNext Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
            (sint.nat wv.index') (sint.Z upto) =
          (expRem Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
            (sint.nat wv.index') (sint.Z upto) (sint.nat r)).head?⌝ : IProp GF)
      $$ [r Hh Hrd keyW end'W revW indexW Hk He c upto w]
  · iexists wv.rev'
    iframe
    ipureintro
    exact ⟨Int.le_refl _, Or.inr rfl, expNext_eq_rem _ _ _ _ _⟩
  wp_for IH
  by_cases Hlt : sint.Z r ≤ sint.Z upto
  rotate_left
  · -- the loop's end: nothing up to `upto`
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hT : expNext Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
        (sint.nat wv.index') (sint.Z upto) = none := by
      rw [Hr.2.2, expRem_end _ _ _ _ _ _ (by word)]; rfl
    wp_auto
    ihave Hw : w ↦{dqw} wv $$ [keyW end'W revW indexW]
    · iapply typedPointsto_combine w _ dqw Hwn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iframe
    ipureintro
    unfold expRes; rw [hT]
  rw [decide_eq_true Hlt]; simp only [↓reduceIte]
  wp_auto
  have hr0 : 0 ≤ sint.Z r := by omega
  wp_apply wp_changesAt h γ Hlb r hr0 (by word) $$ [$Hrd $Hlb] as %sl ⟨Hrd, %chs, #Hs, %Hchs⟩
  ihave %Hsl := ownSlice_len $$ Hs
  have hchs : (Hlb[sint.nat r]?.map Prod.snd).getD [] = chs := by rw [Hchs]; rfl
  ihave IH2 : (∃ (j sn : w64) (chv : change),
      "i" ∷ i_ptr ↦ j ∗ "seen" ∷ seen_ptr ↦ sn ∗ "ch" ∷ ch_ptr ↦ chv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ chs.length ∧ 0 ≤ sint.Z sn ∧
        sint.nat sn = ((chs.take (sint.nat j)).filter
          fun ch => inRangeM (decide (wv.end' = slice.nil)) kk e ch.key').length ∧
        sint.nat sn ≤ expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r)⌝ : IProp GF)
      $$ [i seen ch]
  · iexists W64 0, W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, by word, ?_, by word⟩
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
      List.length_nil]
  wp_for IH2
  by_cases Hlt2 : sint.Z j < sint.Z sl.len
  rotate_left
  · -- the inner loop's end: nothing left at `r`
    rw [decide_eq_false Hlt2]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hjn : sint.nat j = chs.length := by word
    have hrU : (sint.nat r : Int) ≤ sint.Z upto := by
      have : sint.nat r = (sint.Z r).toNat := rfl
      omega
    have hrv : sint.nat wv.rev' ≤ sint.nat r := by have := Hr.1; word
    have hr1 : sint.nat (r + W64 1) = sint.nat r + 1 := by word
    have hd : (rangeChs Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat r)).drop
        (expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r)) = [] := by
      apply rangeChs_drop_nil _ _ _ _ chs hchs
      have h1 := Hj.2.2.2.1
      rw [hjn, List.take_length] at h1
      have h2 := Hj.2.2.2.2
      omega
    (try wp_auto)
    wp_for_post
    iframe
    iexists r + W64 1
    iframe
    ipureintro
    refine ⟨by word, Or.inl (by word), ?_⟩
    rw [Hr.2.2, hr1]
    exact congrArg List.head? (expRem_step _ _ _ _ (sint.Z upto) _ hrv hrU hd)
  rw [decide_eq_true Hlt2]; simp only [↓reduceIte]
  have hjl : sint.nat j < chs.length := by word
  obtain ⟨x, hx⟩ : ∃ x, chs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
  have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hlt2⟩
  (try wp_auto)
  (try simp only [hb, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index sl (sint.Z j) chs DFrac.discard x Hj.1 $$ [Hs] as -
  · iframe #; ipureintro; exact hx
  (try wp_auto)
  wp_apply wp_inRange wv.key' wv.end' kk e x.key' dqk dqe $$ [$Hk $He] as ⟨Hk, He⟩
  have htk := filter_take_succ' chs
    (fun ch => inRangeM (decide (wv.end' = slice.nil)) kk e ch.key') (sint.nat j) x hx
  have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
  cases hin : inRangeM (decide (wv.end' = slice.nil)) kk e x.key'
  · -- not in range: the next change
    simp only [hin, Bool.false_eq_true, ↓reduceIte, List.append_nil] at htk
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, sn, x
    iframe
    ipureintro
    refine ⟨by word, by word, Hj.2.2.1, ?_, Hj.2.2.2.2⟩
    rw [hj1, htk]; exact Hj.2.2.2.1
  -- in range: returned if the skipped ones are done
  simp only [hin, ↓reduceIte] at htk
  have hrN : (sint.nat r : Int) = sint.Z r := by word
  have hfound : sint.nat sn = expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r) →
      expNext Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
        (sint.nat wv.index') (sint.Z upto) = some (sint.nat r, x) := by
    intro hs
    rw [Hr.2.2]
    exact expRem_found _ _ _ _ _ _ (by omega) chs hchs (sint.nat j) x hx hin
      (by rw [← Hj.2.2.2.1]; exact hs)
  have hlenR : (rangeChs Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat r)).length
      < 2 ^ 63 := by
    have h1 : (rangeChs Hlb (inRangeM (decide (wv.end' = slice.nil)) kk e) (sint.nat r)).length
        ≤ chs.length := by
      unfold rangeChs; rw [hchs]; exact List.length_filter_le _ _
    word
  by_cases hgt : sint.Z wv.rev' < sint.Z r
  · -- past the watcher's revision: nothing skipped, this one
    have hT := hfound (by
      have : expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r) = 0 := by
        unfold expSkip; simp only [show sint.nat r ≠ sint.nat wv.rev' by word, ↓reduceIte]
      have := Hj.2.2.2.2; omega)
    (try wp_auto)
    simp only [hgt, _root_.decide_true]
    (try wp_auto)
    wp_for_post
    wp_for_post
    (try wp_auto)
    ihave Hw : w ↦{dqw} wv $$ [keyW end'W revW indexW]
    · iapply typedPointsto_combine w _ dqw Hwn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iframe
    ipureintro
    unfold expRes; rw [hT]
    exact ⟨rfl, rfl, by word, hlenR⟩
  · (try wp_auto)
    rw [decide_eq_false hgt]
    (try wp_auto)
    have hrr : sint.nat r = sint.nat wv.rev' := by have := Hr.1; word
    have hsk : expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r) = sint.nat wv.index' := by
      unfold expSkip; simp only [hrr, ↓reduceIte]
    by_cases hge : sint.Z wv.index' ≤ sint.Z sn
    · -- the skipped ones are done: this one
      have hT := hfound (by have := Hj.2.2.2.2; rw [hsk] at this ⊢; word)
      rw [decide_eq_true hge]
      (try wp_auto)
      wp_for_post
      wp_for_post
      (try wp_auto)
      ihave Hw : w ↦{dqw} wv $$ [keyW end'W revW indexW]
      · iapply typedPointsto_combine w _ dqw Hwn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iapply HΦ
      iframe
      ipureintro
      unfold expRes; rw [hT]
      exact ⟨rfl, rfl, by word, hlenR⟩
    · -- skipped
      rw [decide_eq_false hge]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, sn + W64 1, x
      iframe
      ipureintro
      have hsn : sint.nat (sn + W64 1) = sint.nat sn + 1 := by word
      refine ⟨by word, by word, by word, ?_, ?_⟩
      · rw [hj1, htk, hsn, List.length_append, ← Hj.2.2.2.1]; rfl
      · rw [hsn, hsk]; word

end proof

end mvccrand
end EtcdGrove
end Perennial
