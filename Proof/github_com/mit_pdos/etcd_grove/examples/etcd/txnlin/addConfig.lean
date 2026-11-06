/-
Lean-first (no Rocq counterpart).

The proof of `addConfig`: the binary search's invariant is that the configurations before `lo`
are below `c`'s and those from `hi` on above (`s` is sorted: `CfgSorted`); then the insertion's
loop shifts the configurations from `lo` on one place up (`insCfgL_eq_split`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.addConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpConfig

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

theorem addConfig.wp_proof (wp_cmpConfig : cmpConfig.spec (GF := GF) (hG := hG)) :
    addConfig.spec (GF := GF) (hG := hG) := by
  intro s cs gs c g
  wp_start as ⟨Hs, Hcap, #Hcs, #Hc, %Hsort⟩
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcs
  wp_auto
  ihave HI : (∃ (lo hi : w64),
      "lo" ∷ lo_ptr ↦ lo ∗ "hi" ∷ hi_ptr ↦ hi ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z s.len ∧
        (∀ i < sint.nat lo, ∀ x, gs[i]? = some x → cmpCfgO x g = .lt) ∧
        (∀ i, sint.nat hi ≤ i → ∀ x, gs[i]? = some x → cmpCfgO x g = .gt)⌝ : IProp GF)
    $$ [lo hi]
  · iexists W64 0, s.len
    iframe
    ipureintro
    refine ⟨by word, by word, by word, fun i hi => absurd hi (by word), fun i hi x hx => ?_⟩
    have := (List.getElem?_eq_some_iff.1 hx).1
    word
  wp_for HI
  wp_if_destruct
  · have hm1 : sint.Z (lo + BitVec.sdiv (hi - lo) (W64 2)) = sint.Z lo + (sint.Z hi - sint.Z lo) / 2 := by
      word
    generalize lo + BitVec.sdiv (hi - lo) (W64 2) = mid at hm1 ⊢
    have Hmb : 0 ≤ sint.Z mid ∧ sint.Z mid < sint.Z s.len := ⟨by omega, by omega⟩
    simp only [Hmb, _root_.and_self, ↓reduceIte]
    list_elem cs (sint.nat mid) as cm
    list_elem gs (sint.nat mid) as gm
    wp_apply wp_load_slice_index s (sint.Z mid) cs _ cm Hmb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hcm_lookup
    ihave #Hcm := BigSepL2.bigSepL2_lookup (Φ := fun _ c' g' => cfgOwn (GF := GF) c' g')
      Hcm_lookup Hgm_lookup $$ Hcs
    (try wp_auto)
    wp_apply wp_cmpConfig cm c gm g $$ [$Hcm $Hc]
    wp_if_destruct
    · -- found: `s` unchanged
      have hgm : gm = g := Std.LawfulEqCmp.eq_of_compare ((ordW_eq_zero _).1 Hif)
      have hmem : g ∈ gs := by rw [← hgm]; exact List.mem_of_getElem? Hgm_lookup
      wp_for_post
      iapply HΦ
      rw [addConfigL, if_pos hmem]
      iframe
      iexact Hcs
    · have hne : cmpCfgO gm g ≠ .eq := fun h => Hif ((ordW_eq_zero _).2 h)
      wp_if_destruct
      · -- below `c`: `lo = mid + 1`
        have hlt : cmpCfgO gm g = .lt := (ordW_neg _).1 Hif
        wp_for_post
        iframe
        iexists mid + W64 1, hi
        iframe
        ipureintro
        refine ⟨by word, by word, Hb.2.2.1, fun i hi x hx => ?_, Hb.2.2.2.2⟩
        rcases Nat.lt_or_ge i (sint.nat mid) with h | h
        · exact Std.TransCmp.lt_trans (Hsort.lt h hx Hgm_lookup) hlt
        · have : i = sint.nat mid := by word
          subst this
          rw [Hgm_lookup] at hx; cases hx; exact hlt
      · -- above `c`: `hi = mid`
        have hgt : cmpCfgO gm g = .gt := by
          cases h : cmpCfgO gm g with
          | lt => exact absurd ((ordW_neg _).2 h) Hif
          | eq => exact absurd h hne
          | gt => rfl
        wp_for_post
        iframe
        iexists lo, mid
        iframe
        ipureintro
        refine ⟨Hb.1, by word, by word, Hb.2.2.2.1, fun i hi x hx => ?_⟩
        rcases Nat.lt_or_ge (sint.nat mid) i with h | h
        · exact Std.TransCmp.gt_trans (Std.OrientedCmp.gt_iff_lt.2 (Hsort.lt h Hgm_lookup hx)) hgt
        · have : i = sint.nat mid := by omega
          subst this
          rw [Hgm_lookup] at hx; cases hx; exact hgt
  · -- `c` is not in `s`: its place is `lo`
    have hlohi : sint.Z lo = sint.Z hi := by omega
    have hbelow := Hb.2.2.2.1
    have habove : ∀ i, sint.nat lo ≤ i → ∀ x, gs[i]? = some x → cmpCfgO x g = .gt :=
      fun i hi x hx => Hb.2.2.2.2 i (by word) x hx
    have hnm : g ∉ gs := fun hg => by
      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
      have hx : gs[i]? = some g := by rw [List.getElem?_eq_getElem hi, hgi]
      rcases Nat.lt_or_ge i (sint.nat lo) with h | h
      · have := hbelow i h g hx; rw [Std.ReflCmp.compare_self (cmp := cmpCfgO)] at this; cases this
      · have := habove i h g hx; rw [Std.ReflCmp.compare_self (cmp := cmpCfgO)] at this; cases this
    have hlo : sint.nat lo ≤ cs.length := by word
    have hins := insCfgL_eq_split gs g (sint.nat lo) (by omega) hbelow
      (fun x hx => habove _ (Nat.le_refl _) x hx)
    wp_apply wp_slice_literal (l := [c])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl1, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hl1] as %s' ⟨Hs, Hcap, -⟩
    ihave %Hl' := ownSlice_len $$ Hs
    simp only [List.length_append, List.length_singleton] at Hl'
    ihave HJ : (∃ (j : w64) (x : mcfg),
        "j" ∷ j_ptr ↦ j ∗ "Hs" ∷ s' ↦* (cs.take (sint.nat j) ++ x :: cs.drop (sint.nat j)) ∗
        "%Hj" ∷ ⌜sint.Z lo ≤ sint.Z j ∧ sint.nat j ≤ cs.length⌝ : IProp GF) $$ [j Hs]
    · iexists s'.len - W64 1, c
      have e : sint.nat (s'.len - W64 1) = cs.length := by word
      rw [e, List.take_of_length_le (Nat.le_refl _), List.drop_of_length_le (Nat.le_refl _)]
      iframe
      ipureintro; constructor <;> word
    wp_for HJ
    wp_if_destruct
    · -- `j > lo`: `s[j] = s[j-1]`
      have Hj0 : 0 < sint.nat j := by word
      have e1 : (sint.Z (j - W64 1)).toNat = sint.nat j - 1 := by word
      have Hb1 : 0 ≤ sint.Z (j - W64 1) ∧ sint.Z (j - W64 1) < sint.Z s'.len := by
        constructor <;> word
      simp only [Hb1, _root_.and_self, ↓reduceIte]
      have Hjc : sint.nat j - 1 < cs.length := by omega
      wp_apply wp_load_slice_index s' (sint.Z (j - W64 1)) _ _ cs[sint.nat j - 1] Hb1.1 $$ [Hs]
        as Hs
      · iframe; ipureintro; rw [e1]; exact getElem?_take_drop_pred cs _ x Hj0 Hj.2
      (try wp_auto)
      have Hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s'.len := by constructor <;> word
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index s' (sint.Z j) _ cs[sint.nat j - 1] $$ [Hs] as Hs
      · iframe; ipureintro; constructor
        · word
        · simp; word
      wp_for_post
      iframe
      iexists j - W64 1, cs[sint.nat j - 1]
      have e2 : sint.nat (j - W64 1) = sint.nat j - 1 := by word
      rw [show (sint.Z j).toNat = sint.nat j from rfl, set_at_take_drop cs _ x _ Hj.2,
        take_drop_shift cs _ Hj0 Hj.2, e2]
      iframe
      ipureintro; constructor <;> word
    · -- `j = lo`: `s[lo] = c`
      have hj : sint.nat j = sint.nat lo := by word
      have Hb2 : 0 ≤ sint.Z lo ∧ sint.Z lo < sint.Z s'.len := by constructor <;> word
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index s' (sint.Z lo) _ c $$ [Hs] as Hs
      · iframe; ipureintro; constructor
        · word
        · simp; word
      wp_auto
      rw [show (sint.Z lo).toNat = sint.nat lo from rfl, hj, set_at_take_drop cs _ x _ hlo]
      iapply HΦ
      rw [addConfigL, if_neg hnm, hins]
      iframe
      iapply cfgOwn_insert cs gs (sint.nat lo) c g Hlen
      isplit
      · iexact Hcs
      · iexact Hc

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
