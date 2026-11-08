module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The first `/` at `j`: `splitKeyL` cuts there. -/
theorem splitKeyL_at (key : GoString) (j : Nat) (hj : key[j]? = some (W8 47))
    (hpre : ∀ x ∈ key.take j, x ≠ W8 47) : splitKeyL key = (key.take j, key.drop (j + 1)) := by
  have hl : j < key.length := by
    rcases Nat.lt_or_ge j key.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  have hf : key.findIdx (· = W8 47) = j := by
    rw [List.findIdx_eq hl]
    refine ⟨?_, ?_⟩
    · rw [List.getElem?_eq_getElem hl] at hj; simp [Option.some.inj hj]
    · intro k hk
      have := hpre key[k] (List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩)
      simpa using this
  unfold splitKeyL; rw [hf, if_pos hl]

/-- No `/`: `splitKeyL` is the key and `""`. -/
theorem splitKeyL_none (key : GoString) (h : ∀ x ∈ key, x ≠ W8 47) : splitKeyL key = (key, []) := by
  have : key.findIdx (· = W8 47) = key.length := by
    rw [List.findIdx_eq_length]; intro x hx; simpa using h x hx
  unfold splitKeyL; rw [this, if_neg (by omega)]

theorem splitKey.wp_proof : splitKey.spec (GF := GF) (hG := hG) := by
  intro key
  wp_start as -
  (try wp_auto)
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ key.length ∧ ∀ x ∈ key.take (sint.nat j), x ≠ W8 47⌝ :
      IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · have hlt0 : sint.Z j < sint.Z (W64 (key.length : Int)) := by
      rw [intoVal_eq_iff] at Hif
      exact of_decide_eq_true Hif
    have hlt : sint.nat j < key.length := by word
    have hb : key[sint.nat j]? = some (key.getD (sint.nat j) (W8 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
    rw [if_pos Hj.1, hb]
    (try wp_auto)
    by_cases hs : key.getD (sint.nat j) (W8 0) = W8 47
    · rw [decide_eq_true hs]
      (try wp_auto)
      rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z j ∧ sint.Z j ≤ key.length by
        word)]
      (try wp_auto)
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      rw [if_pos (show 0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ sint.Z (W64 (key.length : Int)) ∧
        sint.Z (W64 (key.length : Int)) ≤ key.length by word)]
      (try wp_auto)
      wp_for_post
      have hat := splitKeyL_at key (sint.nat j) (by rw [hb, hs]) Hj.2.2
      have e2 : List.take (sint.nat (W64 (key.length : Int)) - sint.nat (j + W64 1))
          (List.drop (sint.nat (j + W64 1)) key) = key.drop (sint.nat j + 1) := by
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
          show sint.nat (W64 (key.length : Int)) = key.length by word]
        exact List.take_of_length_le (by simp)
      rw [hat, e2, Nat.sub_zero, List.drop_zero]
      iapply HΦ
      ipureintro; trivial
    · rw [decide_eq_false hs]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1
      iframe
      ipureintro
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 ∧ 0 ≤ sint.Z (j + W64 1) ∧
          sint.Z (j + W64 1) ≤ key.length := by
        have h1 := Hj.1; have h2 := Hj.2.1; clear Hj hs hb; word
      refine ⟨hj1.2.1, hj1.2.2, ?_⟩
      rw [hj1.1, List.take_add_one, hb]
      intro y hy
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact Hj.2.2 y hy
      · exact hs
  · rw [intoVal_eq_iff] at Hif
    have hge : ¬ sint.Z j < sint.Z (W64 (key.length : Int)) := by simpa using Hif
    rw [decide_eq_false hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    have hall : key.take (sint.nat j) = key := List.take_of_length_le (by word)
    rw [splitKeyL_none key (by rw [← hall]; exact Hj.2.2)]
    iapply HΦ
    ipureintro; trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
