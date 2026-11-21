/-
The proof of `sort.symMerge` (`Spec/sort/symMerge.lean`): its code computes
`stableModel.symMergeM` (Löb induction for the two recursive calls, as Perennial's
`sort.pdqsort.wp_proof`).
-/
module

public import Spec.sort.symMerge
public import Spec.sort.rotate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open stableModel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

set_option maxHeartbeats 4000000 in
theorem sort.symMerge.wp_proof (wp_rotate : sort.rotate.spec (GF := GF) (hG := hG)) :
    sort.symMerge.spec (GF := GF) (hG := hG) := fun E x R lt l a m b => by
  iloeb as IH generalizing %l %a %m %b
  irevert IH
  iapply _root_.Perennial.sort.sortHide_intro
  iintro #IH
  wp_start as ⟨#Hs, Hl, %Hb⟩
  ihave #Hsrt := sorterSpec_isSorter x R lt $$ Hs
  wp_auto
  have hlen := Hb.2.2.2.1
  wp_if_destruct
  · -- `m - a == 1`: insert `data[a]` into `[m, b)`
    have hma : sint.nat m = sint.nat a + 1 := by word
    ihave HB : (∃ (i j : w64),
        "i" ∷ i_ptr ↦ i ∗
        "j" ∷ j_ptr ↦ j ∗
        "%Hij" ∷ ⌜sint.Z m ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z b ∧
          bsearch (fun h => lessL lt l h (sint.nat a)) (sint.nat i) (sint.nat j) =
            bsearch (fun h => lessL lt l h (sint.nat a)) (sint.nat m) (sint.nat b)⌝ : IProp GF)
        $$ [i j]
    · iexists m, b; iframe; ipureintro; exact ⟨by word, by word, by word, rfl⟩
    wp_for HB
    obtain ⟨Hij1, Hij2, Hij3, Hbs⟩ := Hij
    wp_if_destruct
    · have Hh : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j ∧
          sint.nat ((i + j) >>> W64 1) = (sint.nat i + sint.nat j) / 2 := by
        rw [_root_.Perennial.sort.shiftr_1_eq_div]; refine ⟨by word, by word, by word⟩
      generalize (i + j) >>> W64 1 = h at Hh ⊢
      list_elem l (sint.nat h) as x0
      list_elem l (sint.nat a) as x1
      wp_apply _root_.Perennial.sort.wp_sorter_Less x R (fun a b => lt a b = true) l h a x0 x1
        (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl] as %r ⟨Hl, %Hr⟩
      have hless : lessL lt l (sint.nat h) (sint.nat a) = lt x0 x1 :=
        lessL_eq lt l _ _ x0 x1 Hx0_lookup Hx1_lookup
      have hunf : bsearch (fun h => lessL lt l h (sint.nat a)) (sint.nat i) (sint.nat j) =
          if lessL lt l (sint.nat h) (sint.nat a) then
            bsearch (fun h => lessL lt l h (sint.nat a)) (sint.nat h + 1) (sint.nat j)
          else bsearch (fun h => lessL lt l h (sint.nat a)) (sint.nat i) (sint.nat h) := by
        conv => lhs; unfold bsearch
        rw [dif_pos (by word), Hh.2.2]
      cases r
      · have hlt : lt x0 x1 = false := by
          cases hc : lt x0 x1
          · rfl
          · exact absurd (Hr.2 hc) (by simp)
        wp_auto
        wp_for_post
        iframe
        iexists i, h
        iframe
        ipureintro
        refine ⟨by word, by word, by word, ?_⟩
        rw [← Hbs, hunf, hless, hlt]; rfl
      · have hlt : lt x0 x1 = true := Hr.1 rfl
        wp_auto
        wp_for_post
        iframe
        iexists (h + W64 1), j
        iframe
        ipureintro
        refine ⟨by word, by word, by word, ?_⟩
        rw [← Hbs, hunf, hless, hlt, show sint.nat (h + W64 1) = sint.nat h + 1 by word]; rfl
    · have hij : sint.Z i = sint.Z j := by omega
      have hk : bsearch (fun h => lessL lt l h (sint.nat a)) (sint.nat m) (sint.nat b) =
          sint.nat i := by
        rw [← Hbs]; unfold bsearch; rw [dif_neg (by word)]
      -- the swaps `Swap(k, k+1)` for `k` from `a` to `i - 2`
      ihave HK : (∃ (k : w64),
          "k" ∷ k_ptr ↦ k ∗
          "Hl" ∷ R (upM l (sint.nat a) (sint.nat k - sint.nat a)) ∗
          "%Hk" ∷ ⌜sint.Z a ≤ sint.Z k ∧ sint.Z k ≤ sint.Z i - 1⌝ : IProp GF) $$ [k Hl]
      · iexists a
        rw [Nat.sub_self]
        iframe
        ipureintro; word
      wp_for HK
      have hulen := upM_length l (sint.nat a) (sint.nat k - sint.nat a)
      wp_if_destruct
      · list_elem (upM l (sint.nat a) (sint.nat k - sint.nat a)) (sint.nat k) as x0
        list_elem (upM l (sint.nat a) (sint.nat k - sint.nat a)) (sint.nat (k + W64 1)) as x1
        wp_apply _root_.Perennial.sort.wp_sorter_Swap x R (fun a b => lt a b = true) _ k
          (k + W64 1) x0 x1 (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl] as Hl
        have heq : upM l (sint.nat a) (sint.nat (k + W64 1) - sint.nat a) =
            <[sint.nat k := x1]> (<[sint.nat (k + W64 1) := x0]>
              (upM l (sint.nat a) (sint.nat k - sint.nat a))) := by
          have e1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          rw [e1] at Hx1_lookup ⊢
          rw [show sint.nat k + 1 - sint.nat a = (sint.nat k - sint.nat a) + 1 by word]
          simp only [upM]
          rw [show sint.nat a + (sint.nat k - sint.nat a) = sint.nat k by word]
          rw [swapL_eq _ _ _ _ _ Hx0_lookup Hx1_lookup]
          exact _root_.Perennial.sort.swap_set_comm _ _ _ _ _ Hx0_lookup Hx1_lookup
        wp_for_post
        iframe
        iexists (k + W64 1)
        rw [heq]
        iframe
        ipureintro
        word
      · iapply HΦ
        rw [symMergeM, dif_pos ⟨by word, by word⟩, if_pos (by word), hk,
          show sint.nat i - 1 - sint.nat a = sint.nat k - sint.nat a by word]
        iexact Hl
  have hma : sint.nat m - sint.nat a ≠ 1 := by
    intro h; apply Hif; word
  clear Hif
  wp_if_destruct
  · -- `b - m == 1`: insert `data[m]` into `[a, m)`
    have hbm : sint.nat b = sint.nat m + 1 := by word
    ihave HB : (∃ (i j : w64),
        "i" ∷ i_ptr ↦ i ∗
        "j" ∷ j_ptr ↦ j ∗
        "%Hij" ∷ ⌜sint.Z a ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z m ∧
          bsearch (fun h => !lessL lt l (sint.nat m) h) (sint.nat i) (sint.nat j) =
            bsearch (fun h => !lessL lt l (sint.nat m) h) (sint.nat a) (sint.nat m)⌝ : IProp GF)
        $$ [i j]
    · iexists a, m; iframe; ipureintro; exact ⟨by word, by word, by word, rfl⟩
    wp_for HB
    obtain ⟨Hij1, Hij2, Hij3, Hbs⟩ := Hij
    wp_if_destruct
    · have Hh : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j ∧
          sint.nat ((i + j) >>> W64 1) = (sint.nat i + sint.nat j) / 2 := by
        rw [_root_.Perennial.sort.shiftr_1_eq_div]; refine ⟨by word, by word, by word⟩
      generalize (i + j) >>> W64 1 = h at Hh ⊢
      list_elem l (sint.nat m) as x0
      list_elem l (sint.nat h) as x1
      wp_apply _root_.Perennial.sort.wp_sorter_Less x R (fun a b => lt a b = true) l m h x0 x1
        (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl] as %r ⟨Hl, %Hr⟩
      have hless : lessL lt l (sint.nat m) (sint.nat h) = lt x0 x1 :=
        lessL_eq lt l _ _ x0 x1 Hx0_lookup Hx1_lookup
      have hunf : bsearch (fun h => !lessL lt l (sint.nat m) h) (sint.nat i) (sint.nat j) =
          if !lessL lt l (sint.nat m) (sint.nat h) then
            bsearch (fun h => !lessL lt l (sint.nat m) h) (sint.nat h + 1) (sint.nat j)
          else bsearch (fun h => !lessL lt l (sint.nat m) h) (sint.nat i) (sint.nat h) := by
        conv => lhs; unfold bsearch
        rw [dif_pos (by word), Hh.2.2]
      cases r
      · have hlt : lt x0 x1 = false := by
          cases hc : lt x0 x1
          · rfl
          · exact absurd (Hr.2 hc) (by simp)
        wp_auto
        wp_for_post
        iframe
        iexists (h + W64 1), j
        iframe
        ipureintro
        refine ⟨by word, by word, by word, ?_⟩
        rw [← Hbs, hunf, hless, hlt, show sint.nat (h + W64 1) = sint.nat h + 1 by word]; rfl
      · have hlt : lt x0 x1 = true := Hr.1 rfl
        wp_auto
        wp_for_post
        iframe
        iexists i, h
        iframe
        ipureintro
        refine ⟨by word, by word, by word, ?_⟩
        rw [← Hbs, hunf, hless, hlt]; rfl
    · have hij : sint.Z i = sint.Z j := by omega
      have hk : bsearch (fun h => !lessL lt l (sint.nat m) h) (sint.nat a) (sint.nat m) =
          sint.nat i := by
        rw [← Hbs]; unfold bsearch; rw [dif_neg (by word)]
      -- the swaps `Swap(k, k-1)` for `k` from `m` down to `i + 1`
      ihave HK : (∃ (k : w64),
          "k" ∷ k_ptr ↦ k ∗
          "Hl" ∷ R (downM l (sint.nat m) (sint.nat m - sint.nat k)) ∗
          "%Hk" ∷ ⌜sint.Z i ≤ sint.Z k ∧ sint.Z k ≤ sint.Z m⌝ : IProp GF) $$ [k Hl]
      · iexists m
        rw [Nat.sub_self]
        iframe
        ipureintro; word
      wp_for HK
      have hdlen := downM_length l (sint.nat m) (sint.nat m - sint.nat k)
      wp_if_destruct
      · list_elem (downM l (sint.nat m) (sint.nat m - sint.nat k)) (sint.nat k) as x0
        list_elem (downM l (sint.nat m) (sint.nat m - sint.nat k)) (sint.nat (k - W64 1)) as x1
        wp_apply _root_.Perennial.sort.wp_sorter_Swap x R (fun a b => lt a b = true) _ k
          (k - W64 1) x0 x1 (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl] as Hl
        have heq : downM l (sint.nat m) (sint.nat m - sint.nat (k - W64 1)) =
            <[sint.nat k := x1]> (<[sint.nat (k - W64 1) := x0]>
              (downM l (sint.nat m) (sint.nat m - sint.nat k))) := by
          have e1 : sint.nat (k - W64 1) = sint.nat k - 1 := by word
          rw [e1] at Hx1_lookup ⊢
          rw [show sint.nat m - (sint.nat k - 1) = (sint.nat m - sint.nat k) + 1 by word]
          simp only [downM]
          rw [show sint.nat m - (sint.nat m - sint.nat k) = sint.nat k by word]
          rw [swapL_eq _ _ _ _ _ Hx0_lookup Hx1_lookup]
          exact _root_.Perennial.sort.swap_set_comm _ _ _ _ _ Hx0_lookup Hx1_lookup
        wp_for_post
        iframe
        iexists (k - W64 1)
        rw [heq]
        iframe
        ipureintro
        word
      · iapply HΦ
        rw [symMergeM, dif_pos ⟨by word, by word⟩, if_neg hma, if_pos (by word), hk,
          show sint.nat i = sint.nat k by word]
        iexact Hl
  have hbm : sint.nat b - sint.nat m ≠ 1 := by
    intro h; apply Hif; word
  clear Hif
  -- the general case
  have Hmid : sint.Z ((a + b) >>> W64 1) = (sint.Z a + sint.Z b) / 2 ∧
      sint.nat ((a + b) >>> W64 1) = (sint.nat a + sint.nat b) / 2 := by
    rw [_root_.Perennial.sort.shiftr_1_eq_div]; exact ⟨by word, by word⟩
  generalize (a + b) >>> W64 1 = mid at Hmid ⊢
  -- `start` and `r`: the binary search's range
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (s0 r0 : w64),
      "start" ∷ start_ptr ↦ s0 ∗ "r" ∷ r_ptr ↦ r0 ∗
      "a" ∷ a_ptr ↦ a ∗ "b" ∷ b_ptr ↦ b ∗ "m" ∷ m_ptr ↦ m ∗ "mid" ∷ mid_ptr ↦ mid ∗
      "n" ∷ n_ptr ↦ (mid + m) ∗
      "%Hsr" ∷ ⌜sint.nat s0 = (if sint.nat mid < sint.nat m then
          sint.nat mid + sint.nat m - sint.nat b else sint.nat a) ∧
        sint.nat r0 = (if sint.nat mid < sint.nat m then sint.nat mid else sint.nat m) ∧
        sint.Z a ≤ sint.Z s0 ∧ sint.Z s0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z m ∧
        sint.Z r0 ≤ sint.Z mid ∧ sint.Z mid + sint.Z m - sint.Z s0 ≤ sint.Z b ∧
        (sint.Z s0 = sint.Z a ∨ sint.Z mid + sint.Z m - sint.Z s0 = sint.Z b) ∧
        (sint.Z r0 = sint.Z m ∨ sint.Z r0 = sint.Z mid)⌝)))
      $$ [start r a b m mid n]
  · wp_if_destruct
    · isplitr
      · ipureintro; trivial
      iexists (mid + m - b), mid
      iframe
      ipureintro
      rw [if_pos (by word), if_pos (by word)]
      refine ⟨by word, by word, by word, by word, by word, by word, by word, by word, by word⟩
    · isplitr
      · ipureintro; trivial
      iexists a, m
      iframe
      ipureintro
      rw [if_neg (by word), if_neg (by word)]
      refine ⟨rfl, rfl, by word, by word, by word, by word, by word, by word, by word⟩
  iintro %v ⟨%Hv, %s0, %r0, Hpost⟩
  subst Hv
  iNamed Hpost
  obtain ⟨Hs0, Hr0, F1, F2, F3, F4, F5, F6, F7⟩ := Hsr
  -- (kept in the Iris context until the end: `word` fails on hypotheses with `if`s)
  ihave Hsr0 : ⌜sint.nat s0 = (if sint.nat mid < sint.nat m then
          sint.nat mid + sint.nat m - sint.nat b else sint.nat a) ∧
        sint.nat r0 = (if sint.nat mid < sint.nat m then sint.nat mid else sint.nat m)⌝ $$ []
  · ipureintro; exact ⟨Hs0, Hr0⟩
  clear Hs0 Hr0
  wp_auto
  -- the binary search for `start`
  ihave HB : (∃ (st rr : w64),
      "start" ∷ start_ptr ↦ st ∗
      "r" ∷ r_ptr ↦ rr ∗
      "%Hsr" ∷ ⌜sint.Z s0 ≤ sint.Z st ∧ sint.Z st ≤ sint.Z rr ∧ sint.Z rr ≤ sint.Z r0 ∧
        bsearch (fun c => !lessL lt l (sint.nat mid + sint.nat m - 1 - c) c) (sint.nat st)
            (sint.nat rr) =
          bsearch (fun c => !lessL lt l (sint.nat mid + sint.nat m - 1 - c) c) (sint.nat s0)
            (sint.nat r0)⌝ : IProp GF) $$ [start r]
  · iexists s0, r0; iframe; ipureintro; exact ⟨by word, by word, by word, rfl⟩
  wp_for HB
  obtain ⟨Hsr1, Hsr2, Hsr3, Hbs⟩ := Hsr
  wp_if_destruct
  · have Hc : sint.Z st ≤ sint.Z ((st + rr) >>> W64 1) ∧
        sint.Z ((st + rr) >>> W64 1) < sint.Z rr ∧
        sint.nat ((st + rr) >>> W64 1) = (sint.nat st + sint.nat rr) / 2 := by
      rw [_root_.Perennial.sort.shiftr_1_eq_div]; refine ⟨by word, by word, by word⟩
    generalize (st + rr) >>> W64 1 = c at Hc ⊢
    have hc1 : sint.nat (c + W64 1) = sint.nat c + 1 := by word
    have hpc : sint.nat (mid + m - W64 1 - c) = sint.nat mid + sint.nat m - 1 - sint.nat c := by
      word
    list_elem l (sint.nat (mid + m - W64 1 - c)) as x0
    list_elem l (sint.nat c) as x1
    wp_apply _root_.Perennial.sort.wp_sorter_Less x R (fun a b => lt a b = true) l
      (mid + m - W64 1 - c) c x0 x1 (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl]
      as %r ⟨Hl, %Hr⟩
    rw [hpc] at Hx0_lookup
    have hless : lessL lt l (sint.nat mid + sint.nat m - 1 - sint.nat c) (sint.nat c) = lt x0 x1 :=
      lessL_eq lt l _ _ x0 x1 Hx0_lookup Hx1_lookup
    have hunf : bsearch (fun c => !lessL lt l (sint.nat mid + sint.nat m - 1 - c) c)
        (sint.nat st) (sint.nat rr) =
        if !lessL lt l (sint.nat mid + sint.nat m - 1 - sint.nat c) (sint.nat c) then
          bsearch (fun c => !lessL lt l (sint.nat mid + sint.nat m - 1 - c) c) (sint.nat c + 1)
            (sint.nat rr)
        else bsearch (fun c => !lessL lt l (sint.nat mid + sint.nat m - 1 - c) c) (sint.nat st)
          (sint.nat c) := by
      conv => lhs; unfold bsearch
      rw [dif_pos (by word), Hc.2.2]
    cases r
    · have hlt : lt x0 x1 = false := by
        cases hc : lt x0 x1
        · rfl
        · exact absurd (Hr.2 hc) (by simp)
      wp_auto
      wp_for_post
      iframe
      iexists (c + W64 1), rr
      iframe
      ipureintro
      refine ⟨by word, by word, by word, ?_⟩
      rw [← Hbs, hunf, hless, hlt, hc1]; rfl
    · have hlt : lt x0 x1 = true := Hr.1 rfl
      wp_auto
      wp_for_post
      iframe
      iexists st, c
      iframe
      ipureintro
      refine ⟨by word, by word, by word, ?_⟩
      rw [← Hbs, hunf, hless, hlt]; rfl
  have hst : sint.Z st = sint.Z rr := by omega
  have Hstart : bsearch (fun c => !lessL lt l (sint.nat mid + sint.nat m - 1 - c) c)
      (sint.nat s0) (sint.nat r0) = sint.nat st := by
    rw [← Hbs]; unfold bsearch; rw [dif_neg (by word)]
  clear Hbs
  have Hend : sint.Z (mid + m - st) = sint.Z mid + sint.Z m - sint.Z st ∧
      sint.nat (mid + m - st) = sint.nat mid + sint.nat m - sint.nat st := ⟨by word, by word⟩
  -- the rotation
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (L1 : List E),
      "Hl" ∷ R L1 ∗ "start" ∷ start_ptr ↦ st ∗ "m" ∷ m_ptr ↦ m ∗
      "endp" ∷ end_ptr ↦ (mid + m - st) ∗ "data" ∷ data_ptr ↦ GoInterface.ok x ∗
      "%HL1" ∷ ⌜L1 = (if sint.nat st < sint.nat m ∧
          sint.nat m < sint.nat mid + sint.nat m - sint.nat st then
          rotateM l (sint.nat st) (sint.nat m) (sint.nat mid + sint.nat m - sint.nat st) else l)⌝)))
      $$ [Hl start m «end» data]
  · by_cases h1 : sint.Z st < sint.Z m
    · simp only [h1, decide_true]
      wp_auto
      by_cases h2 : sint.Z m < sint.Z (mid + m - st)
      · simp only [h2, decide_true]
        wp_auto
        wp_apply wp_rotate E x R lt l st m (mid + m - st) $$ [Hl] as Hl
        · iframe Hl; iframe #; ipureintro; word
        isplitr
        · ipureintro; trivial
        iexists _
        iframe
        ipureintro
        rw [if_pos ⟨by word, by word⟩, ← Hend.2]
      · simp only [h2, decide_false]
        wp_auto
        isplitr
        · ipureintro; trivial
        iexists l
        iframe
        ipureintro
        rw [if_neg (by word)]
    · simp only [h1, decide_false]
      wp_auto
      isplitr
      · ipureintro; trivial
      iexists l
      iframe
      ipureintro
      rw [if_neg (by word)]
  iintro %v ⟨%Hv, %L1, Hpost⟩
  subst Hv
  iNamed Hpost
  wp_auto
  have hL1len : L1.length = l.length := by
    rw [HL1]; split
    · exact rotateM_length ..
    · rfl
  -- (unhidden before the pure steps of the `if`s, which strip its `▷`)
  irevert IH
  iapply _root_.Perennial.sort.sortHide_elim
  iintro #IH
  -- the first recursive call, on `[a, mid)`
  wp_bind (if: _ then _ else _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (L2 : List E),
      "Hl" ∷ R L2 ∗ "a" ∷ a_ptr ↦ a ∗ "start" ∷ start_ptr ↦ st ∗ "mid" ∷ mid_ptr ↦ mid ∗
      "data" ∷ data_ptr ↦ GoInterface.ok x ∗
      "%HL2" ∷ ⌜L2 = (if sint.nat a < sint.nat st ∧ sint.nat st < sint.nat mid then
          symMergeM lt L1 (sint.nat a) (sint.nat st) (sint.nat mid) else L1)⌝)))
      $$ [Hl a start mid data]
  · by_cases h1 : sint.Z a < sint.Z st
    · simp only [h1, decide_true]
      wp_auto
      by_cases h2 : sint.Z st < sint.Z mid
      · simp only [h2, decide_true]
        wp_auto
        wp_apply IH $$ %L1 %a %st %mid [Hl] as Hl
        · iframe Hl; iframe #; ipureintro; word
        isplitr
        · ipureintro; trivial
        iexists _
        iframe
        ipureintro
        rw [if_pos ⟨by word, by word⟩]
      · simp only [h2, decide_false]
        wp_auto
        isplitr
        · ipureintro; trivial
        iexists L1
        iframe
        ipureintro
        rw [if_neg (by word)]
    · simp only [h1, decide_false]
      wp_auto
      isplitr
      · ipureintro; trivial
      iexists L1
      iframe
      ipureintro
      rw [if_neg (by word)]
  iintro %v ⟨%Hv, %L2, Hpost⟩
  subst Hv
  iNamed Hpost
  wp_auto
  have hL2len : L2.length = l.length := by
    rw [HL2]; split
    · rw [symMergeM_length, hL1len]
    · exact hL1len
  -- the second, on `[mid, b)`
  icases Hsr0 with %Hsr0
  have hfin : symMergeM lt l (sint.nat a) (sint.nat m) (sint.nat b) =
      if sint.nat mid < sint.nat mid + sint.nat m - sint.nat st ∧
        sint.nat mid + sint.nat m - sint.nat st < sint.nat b then
        symMergeM lt L2 (sint.nat mid) (sint.nat mid + sint.nat m - sint.nat st) (sint.nat b)
      else L2 := by
    rw [symMergeM, dif_pos ⟨by word, by word⟩, if_neg hma, if_neg hbm]
    simp only []
    rw [← Hmid.2, ← Hsr0.1, ← Hsr0.2, Hstart, ← HL1, ← HL2]
  by_cases h1 : sint.Z mid < sint.Z (mid + m - st)
  · simp only [h1, decide_true]
    wp_auto
    by_cases h2 : sint.Z (mid + m - st) < sint.Z b
    · simp only [h2, decide_true]
      wp_auto
      wp_apply IH $$ %L2 %mid %(mid + m - st) %b [Hl] as Hl
      · iframe Hl; iframe #; ipureintro; word
      iapply HΦ
      rw [hfin, if_pos ⟨by word, by word⟩, ← Hend.2]
      iexact Hl
    · simp only [h2, decide_false]
      wp_auto
      iapply HΦ
      rw [hfin, if_neg (by word)]
      iexact Hl
  · simp only [h1, decide_false]
    wp_auto
    iapply HΦ
    rw [hfin, if_neg (by word)]
    iexact Hl
