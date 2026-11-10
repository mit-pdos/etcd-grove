/- Lean-first (no Rocq counterpart). The proof of `stream.expect` (mvccrand's `watchCheck.expect`, with `matches`).

The callees in call order: `history.changesAt`, `watcher.matches`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__changesAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.watcher__matches
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LeafLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem stream.expect.wp_proof
    (wp_history_changesAt : history.changesAt.spec (GF := GF) (hG := hG))
    (wp_watcher_matches : watcher.matches.spec (GF := GF) (hG := hG)) :
    stream.expect.spec (GF := GF) (hG := hG) := by
  intro s x h γh Hlb w wv kk e upto dqw dqk dqe hrev0 hidx0 hupto hupto'
  wp_start as ⟨#Hx, #Hh, Hw, Hk, He, Hrd, #Hlb⟩
  icases watcher_pos_split w wv dqw $$ Hw with ⟨revW, indexW, Hback⟩
  wp_auto
  ihave Hw := Hback $$ revW indexW
  ihave IH : (∃ (r : w64),
      "r" ∷ r_ptr ↦ r ∗ "Hrd" ∷ histRd h γh ∗ "Hw" ∷ w ↦{dqw} wv ∗
      "Hk" ∷ wv.key' ↦*{dqk} kk ∗ "He" ∷ wv.end' ↦*{dqe} e ∗
      "s" ∷ s_ptr ↦ s ∗ "upto" ∷ upto_ptr ↦ upto ∗ "w" ∷ w_ptr ↦ w ∗
      "%Hr" ∷ ⌜sint.Z wv.rev' ≤ sint.Z r ∧ (sint.Z r ≤ sint.Z upto + 1 ∨ r = wv.rev') ∧
        expNext Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
            (sint.nat wv.index') (sint.Z upto) =
          (expRem Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
            (sint.nat wv.index') (sint.Z upto) (sint.nat r)).head?⌝ : IProp GF)
      $$ [r Hrd Hw Hk He s upto w]
  · iexists wv.rev'
    iframe
    ipureintro
    exact ⟨Int.le_refl _, Or.inr rfl, expNext_eq_rem _ _ _ _ _⟩
  wp_for IH
  by_cases Hlt : sint.Z r ≤ sint.Z upto
  rotate_left
  · -- the loop's end: nothing up to `upto`
    rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hT : expNext Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e)
        (sint.nat wv.rev') (sint.nat wv.index') (sint.Z upto) = none := by
      rw [Hr.2.2, expRem_end _ _ _ _ _ _ (by word)]; rfl
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    unfold expRes; rw [hT]
  rw [decide_eq_true Hlt]; simp only [↓reduceIte]
  wp_auto
  have hr0 : 0 ≤ sint.Z r := by omega
  wp_apply wp_history_changesAt h γh Hlb r hr0 (by word) $$ [$Hrd $Hlb] as
    %sl ⟨Hrd, %chs, #Hs, %Hchs⟩
  ihave %Hsl := ownSlice_len $$ Hs
  have hchs : (Hlb[sint.nat r]?.map Prod.snd).getD [] = chs := by rw [Hchs]; rfl
  ihave IH2 : (∃ (j sn : w64) (chv : change),
      "i" ∷ i_ptr ↦ j ∗ "seen" ∷ seen_ptr ↦ sn ∗ "ch" ∷ ch_ptr ↦ chv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ chs.length ∧ 0 ≤ sint.Z sn ∧
        sint.nat sn = ((chs.take (sint.nat j)).filter
          (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e)).length ∧
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
    have hd : (rangeChs Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat r)).drop
        (expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r)) = [] := by
      apply rangeChs_drop_nil _ _ _ _ chs hchs
      have h1 := Hj.2.2.2.1
      rw [hjn, List.take_length] at h1
      have h2 := Hj.2.2.2.2
      exact Nat.le_trans (Nat.le_of_eq h1.symm) h2
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
  wp_apply wp_watcher_matches w wv dqw dqk dqe kk e x $$ [$Hw $Hk $He] as ⟨Hw, Hk, He⟩
  · iframe #
  have htk := filter_take_succ' chs (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat j) x hx
  have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
  cases hin : matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e x
  · -- not expected: the next change
    simp only [hin, Bool.false_eq_true, ↓reduceIte, List.append_nil] at htk
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, sn, x
    iframe
    ipureintro
    refine ⟨by word, by word, Hj.2.2.1, ?_, Hj.2.2.2.2⟩
    rw [hj1, htk]; exact Hj.2.2.2.1
  -- expected: returned if the skipped ones are done
  simp only [hin, ↓reduceIte] at htk
  have hrN : (sint.nat r : Int) = sint.Z r := by word
  have hfound : sint.nat sn = expSkip (sint.nat wv.rev') (sint.nat wv.index') (sint.nat r) →
      expNext Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat wv.rev')
        (sint.nat wv.index') (sint.Z upto) = some (sint.nat r, x) := by
    intro hs
    rw [Hr.2.2]
    exact expRem_found _ _ _ _ _ _ (by omega) chs hchs (sint.nat j) x hx hin
      (by rw [← Hj.2.2.2.1]; exact hs)
  have hlenR : (rangeChs Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat r)).length
      < 2 ^ 63 := by
    have h1 : (rangeChs Hlb (matchesM wv.filter' (decide (wv.end' = slice.nil)) kk e) (sint.nat r)).length
        ≤ chs.length := by
      unfold rangeChs; rw [hchs]; exact List.length_filter_le _ _
    word
  icases watcher_pos_split w wv dqw $$ Hw with ⟨revW, indexW, Hback⟩
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
    ihave Hw := Hback $$ revW indexW
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
      ihave Hw := Hback $$ revW indexW
      iapply HΦ
      iframe
      ipureintro
      unfold expRes; rw [hT]
      exact ⟨rfl, rfl, by word, hlenR⟩
    · -- skipped
      rw [decide_eq_false hge]
      (try wp_auto)
      ihave Hw := Hback $$ revW indexW
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

end mvccfull
end EtcdGrove
end Perennial
