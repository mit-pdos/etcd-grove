/- Lean-first (no Rocq counterpart). The proof of `pick.specW` (the weights summed without wrapping,
then the chosen one found at a positive weight; `LeafLemmas.lean`'s `psum`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pickW
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LeafLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem pick.wp_proofW
    (wp_choose : choose.spec (GF := GF) (hG := hG)) :
    pick.specW (GF := GF) (hG := hG) := by
  intro w ws dq n
  wp_start as Hw
  ihave %Hwl := ownSlice_len $$ Hw
  wp_auto
  have hget : ∀ (k : Nat) (v : w64), ws[k]? = some v → (ws.map sint.Z).getD k 0 = sint.Z v := by
    intro k v hv; simp [List.getD, List.getElem?_map, hv]
  ihave IH : (∃ (j tot : w64),
      "i" ∷ i_ptr ↦ j ∗ "total" ∷ total_ptr ↦ tot ∗ "w" ∷ w_ptr ↦ w ∗ "n" ∷ n_ptr ↦ n ∗
      "Hw" ∷ w ↦*{dq} ws ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ (j = W64 0 ∨ sint.Z j ≤ sint.Z n) ∧ sint.Z j ≤ sint.Z w.len ∧
        (j = W64 0 → tot = W64 0) ∧
        (psum (ws.map sint.Z) (sint.nat j) < 2 ^ 63 →
          sint.Z tot = psum (ws.map sint.Z) (sint.nat j))⌝ : IProp GF)
      $$ [i total w n Hw]
  · iexists W64 0, W64 0
    iframe
    ipureintro
    refine ⟨by word, Or.inl rfl, by word, fun _ => rfl, fun _ => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, psum_zero]; rfl
  wp_for IH
  obtain ⟨hj0, hjn, hjl, hj0t, hjt⟩ := Hj
  by_cases Hc : sint.Z j < sint.Z n ∧ sint.Z j < sint.Z w.len
  · rw [decide_eq_true Hc.1]
    (try wp_auto)
    rw [decide_eq_true Hc.2]
    (try simp only [↓reduceIte, decide_true, decide_True_any])
    (try wp_auto)
    have hjl' : sint.nat j < ws.length := by rw [Hwl.1]; word
    list_elem ws (sint.nat j) as wj
    (try simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z w.len from ⟨hj0, Hc.2⟩,
      _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index w (sint.Z j) ws dq wj hj0 $$ [Hw] as Hw
    · iframe; ipureintro; exact Hwj_lookup
    have hz := hget _ _ Hwj_lookup
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hps := psum_succ (ws.map sint.Z) (sint.nat j)
    rw [hz] at hps
    have hpn := psum_nonneg (ws.map sint.Z) (sint.nat j)
    have hjne : j + W64 1 ≠ W64 0 := by intro h; have := congrArg sint.Z h; word
    by_cases hpos : sint.Z (W64 0) < sint.Z wj
    · rw [decide_eq_true hpos]
      (try wp_auto)
      (try simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z w.len from ⟨hj0, Hc.2⟩,
        _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index w (sint.Z j) ws dq wj hj0 $$ [Hw] as Hw
      · iframe; ipureintro; exact Hwj_lookup
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, tot + wj
      iframe
      ipureintro
      refine ⟨by word, Or.inr (by word), by word, fun h => absurd h hjne, fun hlt => ?_⟩
      rw [hj1] at hlt ⊢
      have h1 : psum (ws.map sint.Z) (sint.nat j) < 2 ^ 63 := by
        have := psum_mono (ws.map sint.Z) (Nat.le_succ (sint.nat j)); omega
      have h2 := hjt h1
      have h3 : max 0 (sint.Z wj) = sint.Z wj := by
        have : (0 : Int) < sint.Z wj := by simpa using hpos
        omega
      rw [h3] at hps
      rw [hps, ← h2]
      have : (0 : Int) < sint.Z wj := by simpa using hpos
      word
    · rw [decide_eq_false hpos]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, tot
      iframe
      ipureintro
      refine ⟨by word, Or.inr (by word), by word, fun h => absurd h hjne, fun hlt => ?_⟩
      rw [hj1] at hlt ⊢
      have h3 : max 0 (sint.Z wj) = 0 := by
        have : ¬ (0 : Int) < sint.Z wj := by simpa using hpos
        omega
      rw [h3, Int.add_zero] at hps
      rw [hps] at hlt ⊢
      exact hjt hlt
  have hS : 0 < sint.Z n →
      psum (ws.map sint.Z) (sint.nat n) = psum (ws.map sint.Z) (sint.nat j) := by
    intro hn
    apply psum_exit
    · rw [List.length_map, Hwl.1]; word
    · rcases hjn with h | h
      · rw [h]; exact Nat.zero_le _
      · word
    · rw [List.length_map, Hwl.1]
      by_cases h1 : sint.Z j < sint.Z n
      · exact Or.inr (by have := fun h2 => Hc ⟨h1, h2⟩; word)
      · exact Or.inl (by word)
  by_cases h1 : sint.Z j < sint.Z n
  all_goals first
    | (rw [decide_eq_true h1]; (try wp_auto); rw [decide_eq_false (fun h2 => Hc ⟨h1, h2⟩)])
    | rw [decide_eq_false h1]
  all_goals
    (try simp only [intoVal_eq_iff])
    (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
    (try simp only [intoVal_eq_iff])
    (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
    (try wp_auto)
    (try simp only [intoVal_eq_iff])
    (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
    (try simp only [intoVal_eq_iff])
    (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
    (try wp_auto)
    have hPm : (∃ i : Nat, (i : Int) < sint.Z n ∧ 0 < (ws.map sint.Z).getD i 0) →
        psum (ws.map sint.Z) (sint.nat n) < 2 ^ 63 →
        0 < sint.Z n ∧ 0 < psum (ws.map sint.Z) (sint.nat n) ∧
          sint.Z tot = psum (ws.map sint.Z) (sint.nat n) := by
      intro ⟨i0, hi0, hw0⟩ hlt
      have hn : 0 < sint.Z n := by omega
      have h1 := psum_ge (ws.map sint.Z) (show i0 < sint.nat n by word)
      have h2 := hS hn
      refine ⟨hn, by omega, ?_⟩
      rw [h2] at hlt ⊢
      exact hjt hlt
    by_cases htot : sint.Z tot ≤ sint.Z (W64 0)
    · rw [decide_eq_true htot]
      (try wp_auto)
      wp_apply wp_choose as %x %Hx
      (try wp_auto)
      iapply HΦ
      iframe
      ipureintro
      refine ⟨Hx, fun hP hlt => ?_⟩
      have := hPm hP hlt
      exfalso; have h0 : sint.Z (W64 0) = 0 := rfl; omega
    rw [decide_eq_false htot]
    (try wp_auto)
    have hjne : j ≠ W64 0 := fun h => htot (by rw [hj0t h]; exact Int.le_refl _)
    have hn : 0 < sint.Z n := by
      rcases hjn with h | h
      · exact absurd h hjne
      · have : sint.Z j ≠ 0 := fun h' => hjne (by word)
        omega
    wp_apply wp_choose as %r %Hr
    (try wp_auto)
    have htotS := fun hP hlt => (hPm hP hlt).2.2
    ihave IH2 : (∃ (j2 rc : w64),
        "i" ∷ i_ptr ↦ j2 ∗ "r" ∷ r_ptr ↦ rc ∗ "w" ∷ w_ptr ↦ w ∗ "n" ∷ n_ptr ↦ n ∗
        "Hw" ∷ w ↦*{dq} ws ∗
        "%Hj2" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.Z j2 ≤ sint.Z n ∧ sint.Z j2 ≤ sint.Z w.len ∧
          ((∃ i : Nat, (i : Int) < sint.Z n ∧ 0 < (ws.map sint.Z).getD i 0) →
            psum (ws.map sint.Z) (sint.nat n) < 2 ^ 63 →
            0 ≤ sint.Z rc ∧ sint.Z rc + psum (ws.map sint.Z) (sint.nat j2) = sint.Z r)⌝ : IProp GF)
        $$ [i r w n Hw]
    · iexists W64 0, r
      iframe
      ipureintro
      refine ⟨by word, by word, by word, fun _ _ => ⟨Hr.1, ?_⟩⟩
      rw [show sint.nat (W64 0) = 0 from rfl, psum_zero, Int.add_zero]
    wp_for IH2
    obtain ⟨hk0, hkn, hkl, hkr⟩ := Hj2
    by_cases Hc2 : sint.Z j2 < sint.Z n ∧ sint.Z j2 < sint.Z w.len
    · rw [decide_eq_true Hc2.1]
      (try wp_auto)
      rw [decide_eq_true Hc2.2]
      (try simp only [↓reduceIte, decide_true, decide_True_any])
      (try wp_auto)
      have hjl' : sint.nat j2 < ws.length := by rw [Hwl.1]; word
      list_elem ws (sint.nat j2) as wj
      have hz := hget _ _ Hwj_lookup
      have hj1 : sint.nat (j2 + W64 1) = sint.nat j2 + 1 := by word
      have hps := psum_succ (ws.map sint.Z) (sint.nat j2)
      rw [hz] at hps
      (try simp only [show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z w.len from ⟨hk0, Hc2.2⟩,
        _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index w (sint.Z j2) ws dq wj hk0 $$ [Hw] as Hw
      · iframe; ipureintro; exact Hwj_lookup
      (try wp_auto)
      by_cases hpos : sint.Z (W64 0) < sint.Z wj
      · rw [decide_eq_true hpos]
        (try wp_auto)
        (try simp only [show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z w.len from ⟨hk0, Hc2.2⟩,
          _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index w (sint.Z j2) ws dq wj hk0 $$ [Hw] as Hw
        · iframe; ipureintro; exact Hwj_lookup
        (try wp_auto)
        have hwp : (0 : Int) < sint.Z wj := by simpa using hpos
        by_cases hlt : sint.Z rc < sint.Z wj
        · rw [decide_eq_true hlt]
          (try wp_auto)
          wp_for_post
          (try wp_auto)
          iapply HΦ
          iframe
          ipureintro
          refine ⟨⟨hk0, fun _ => Hc2.1, fun h => absurd h (by omega)⟩, fun _ _ => ?_⟩
          rw [hz]; exact hwp
        rw [decide_eq_false hlt]
        (try wp_auto)
        (try simp only [show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z w.len from ⟨hk0, Hc2.2⟩,
          _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index w (sint.Z j2) ws dq wj hk0 $$ [Hw] as Hw
        · iframe; ipureintro; exact Hwj_lookup
        (try wp_auto)
        wp_for_post
        iframe
        iexists j2 + W64 1, rc - wj
        iframe
        ipureintro
        refine ⟨by word, by word, by word, fun hP hlt' => ?_⟩
        obtain ⟨h1, h2⟩ := hkr hP hlt'
        have h3 : max 0 (sint.Z wj) = sint.Z wj := by omega
        rw [h3] at hps
        rw [hj1, hps]
        refine ⟨by word, ?_⟩
        have : sint.Z (rc - wj) = sint.Z rc - sint.Z wj := by word
        omega
      · rw [decide_eq_false hpos]
        (try wp_auto)
        wp_for_post
        iframe
        iexists j2 + W64 1, rc
        iframe
        ipureintro
        refine ⟨by word, by word, by word, fun hP hlt' => ?_⟩
        obtain ⟨h1, h2⟩ := hkr hP hlt'
        have h3 : max 0 (sint.Z wj) = 0 := by
          have : ¬ (0 : Int) < sint.Z wj := by simpa using hpos
          omega
        rw [h3, Int.add_zero] at hps
        rw [hj1, hps]
        exact ⟨h1, h2⟩
    by_cases h1 : sint.Z j2 < sint.Z n
    all_goals first
      | (rw [decide_eq_true h1]; (try wp_auto); rw [decide_eq_false (fun h2 => Hc2 ⟨h1, h2⟩)])
      | rw [decide_eq_false h1]
    all_goals
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try wp_auto)
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try wp_auto)
      iapply HΦ
      iframe
      ipureintro
      refine ⟨⟨by word, fun _ => by word, fun h => absurd h (by omega)⟩, fun hP hlt => ?_⟩
      exfalso
      obtain ⟨h1', h2'⟩ := hkr hP hlt
      have h3 := htotS hP hlt
      have h4 : psum (ws.map sint.Z) (sint.nat n) = psum (ws.map sint.Z) (sint.nat j2) := by
        apply psum_exit
        · rw [List.length_map, Hwl.1]; word
        · word
        · rw [List.length_map, Hwl.1]
          by_cases h5 : sint.Z j2 < sint.Z n
          · exact Or.inr (by have := fun h2 => Hc2 ⟨h5, h2⟩; word)
          · exact Or.inl (by word)
      have h6 := (hPm hP hlt).2.1
      have h7 := Hr.2.1 (by omega)
      omega

end proof

end mvccfull
end EtcdGrove
end Perennial
