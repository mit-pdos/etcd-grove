/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `stringsEqual`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.stringsEqual

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem stringsEqual.wp_proof : stringsEqual.spec (GF := GF) (hG := hG) := by
  intro al a bl b
  wp_start as ⟨#Ha, #Hb⟩
  iunfold strsRO at Ha Hb
  ihave %Hal := ownSlice_len $$ Ha
  ihave %Hbl := ownSlice_len $$ Hb
  wp_auto
  wp_if_destruct
  · have hab : a.length = b.length := by rw [Hal.1, Hbl.1, Hif]
    ihave IH : iprop(∃ (n kv : w64),
        "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z al.len ∧ a.take (sint.nat n) = b.take (sint.nat n)⌝)
        $$ [i k]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IH
    obtain ⟨hn0, hn1, hnt⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < a.length := by rw [Hal.1]; word
      obtain ⟨x, Hx⟩ : ∃ x, a[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨y, Hy⟩ : ∃ y, b[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem (hab ▸ Hlt)⟩
      have Hif' : sint.Z n < sint.Z bl.len := by
        have : sint.nat n < b.length := hab ▸ Hlt
        rw [Hbl.1] at this; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z al.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index al (sint.Z n) a DFrac.discard x hn0 $$ [Ha] as -
      · isplitr
        · iexact Ha
        ipureintro; exact Hx
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z al.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index al (sint.Z n) a DFrac.discard x hn0 $$ [Ha] as -
      · isplitr
        · iexact Ha
        ipureintro; exact Hx
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z bl.len from ⟨hn0, Hif'⟩))]
      wp_apply wp_load_slice_index bl (sint.Z n) b DFrac.discard y hn0 $$ [Hb] as -
      · isplitr
        · iexact Hb
        ipureintro; exact Hy
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, List.take_add_one,
          hnt, Hx, Hy, Hif]
      · -- `a[k] != b[k]`
        try wp_auto
        wp_for_post
        try wp_auto
        have : decide (a = b) = false := by
          rw [decide_eq_false_iff_not]; intro h
          rw [h, Hy] at Hx; cases Hx
          exact Hif rfl
        rw [this]
        iapply HΦ; ipureintro; trivial
    · try wp_auto
      have hnx : sint.nat n = a.length := by rw [Hal.1]; word
      have : decide (a = b) = true := by
        rw [decide_eq_true_iff]
        rw [hnx, List.take_length, hab, List.take_length] at hnt
        exact hnt
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : decide (a = b) = false := by
      rw [decide_eq_false_iff_not]; intro h
      apply Hif
      have := congrArg List.length h
      rw [Hal.1, Hbl.1] at this; word
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
