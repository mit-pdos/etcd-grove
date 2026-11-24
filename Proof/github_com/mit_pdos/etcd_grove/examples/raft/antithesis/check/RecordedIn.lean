/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `RecordedIn` (B 109-112).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.RecordedIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem RecordedIn.wp_proof (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG)) :
    RecordedIn.spec (GF := GF) (hG := hG) := by
  intro chl ch tll tl ll l c t b
  wp_start as ⟨#Hch, #Htl, #Hl, %Hb⟩
  ihave %Hchl := logRO_len _ _ $$ Hch
  ihave %Hll := logRO_len _ _ $$ Hl
  iunfold termIntsRO at Htl
  icases Htl with ⟨%gs, #Hgs, %Hgf⟩
  ihave %Hgsl := ownSlice_len $$ Hgs
  unfold recordedIn at Hb
  wp_auto
  have hgl : gs.length = tl.length := List.Forall₂.length_eq Hgf
  by_cases hc : sint.Z c ≤ l.length ∧ sint.Z c ≤ ch.length
  case neg =>
    have hb : b = false := by
      have : (decide (sint.Z c ≤ l.length) && decide (sint.Z c ≤ ch.length)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      rw [this] at Hb; simp at Hb; exact Hb
    subst hb
    by_cases hc1 : sint.Z c ≤ sint.Z ll.len
    · rw [decide_eq_true hc1]
      try wp_auto
      have hc2 : ¬ sint.Z c ≤ sint.Z chl.len := by omega
      rw [decide_eq_false hc2]
      try wp_auto
      iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hc1]
      try wp_auto
      iapply HΦ; ipureintro; trivial
  have hc1 : sint.Z c ≤ sint.Z ll.len := by omega
  have hc2 : sint.Z c ≤ sint.Z chl.len := by omega
  rw [decide_eq_true hc1]
  try wp_auto
  rw [decide_eq_true hc2]
  try wp_auto
  have : (decide (sint.Z c ≤ l.length) && decide (sint.Z c ≤ ch.length)) = true := by simp; omega
  rw [this] at Hb
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hb
  ihave IH : iprop(∃ (n : w64) (pv : G.TermInt),
      "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ pv ∗ "found" ∷ found_ptr ↦ false ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z tll.len ∧
        ∀ k (h : k < tl.length), k < sint.nat n → ¬ (tl[k].1 ≤ sint.Z t ∧ tl[k].2 ≥ sint.Z c)⌝) $$ [i p found]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨Int.le_refl _, Hgsl.2, fun k _ hk => absurd hk (Nat.not_lt_zero _)⟩
  wp_for IH
  obtain ⟨hn0, hn1, hall⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < gs.length := by rw [Hgsl.1]; word
    obtain ⟨gp, Hgp⟩ : ∃ x, gs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hlt' : sint.nat n < tl.length := by rw [← hgl]; exact Hlt
    have hrel := forall₂_getElem Hgf (sint.nat n) Hlt Hlt'
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z tll.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index tll (sint.Z n) gs DFrac.discard gs[sint.nat n] hn0 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; rw [show (sint.Z n).toNat = sint.nat n by word]; exact List.getElem?_eq_getElem Hlt
    try wp_auto
    by_cases hfound : sint.Z gs[sint.nat n].T' ≤ sint.Z t ∧ sint.Z gs[sint.nat n].V' ≥ sint.Z c
    · rw [decide_eq_true hfound.1]
      try wp_auto
      rw [decide_eq_true hfound.2]
      try wp_auto
      wp_for_post
      try wp_auto
      -- found: the prefixes
      have hany : (tl.any fun p => decide (p.1 ≤ sint.Z t) && decide (p.2 ≥ sint.Z c)) = true := by
        rw [List.any_eq_true]
        exact ⟨tl[sint.nat n], List.getElem_mem Hlt', by rw [← hrel.1, ← hrel.2]; simpa using hfound⟩
      rw [hany] at Hb
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hb
      obtain ⟨xs, hxs, Hb⟩ := bind_ok Hb
      obtain ⟨ys, hys, Hb⟩ := bind_ok Hb
      wp_apply wp_SubSeq chl ch (W64 1) c xs $$ [Hch] as %xsl #Hxs
      · iframe Hch; ipureintro; exact hxs
      try wp_auto
      wp_apply wp_SubSeq ll l (W64 1) c ys $$ [Hl] as %ysl #Hys
      · iframe Hl; ipureintro; exact hys
      try wp_auto
      wp_apply wp_EntriesEqual xsl xs ysl ys b $$ [Hxs Hys]
      · iframe Hxs Hys; ipureintro; exact Hb
      try wp_auto
      iapply HΦ; ipureintro; trivial
    · have hno : ¬ (sint.Z gs[sint.nat n].T' ≤ sint.Z t ∧ sint.Z gs[sint.nat n].V' ≥ sint.Z c) := hfound
      by_cases hT : sint.Z gs[sint.nat n].T' ≤ sint.Z t
      · rw [decide_eq_true hT]
        try wp_auto
        rw [decide_eq_false (fun h => hno ⟨hT, h⟩)]
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        have hn' := sint_add_one_lt Hif
        have hnn := sint_nat_cast (k := n + W64 1) (by omega)
        have hnn0 := sint_nat_cast hn0
        refine ⟨by omega, by omega, fun k hk hkn => ?_⟩
        by_cases hkk : k < sint.nat n
        · exact hall k hk hkk
        · have hkeq : k = sint.nat n := by omega
          have e : tl[k] = tl[sint.nat n]'Hlt' := by simp only [hkeq]
          rw [e, ← hrel.1, ← hrel.2]; exact hno
      · rw [decide_eq_false hT]
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        have hn' := sint_add_one_lt Hif
        have hnn := sint_nat_cast (k := n + W64 1) (by omega)
        have hnn0 := sint_nat_cast hn0
        refine ⟨by omega, by omega, fun k hk hkn => ?_⟩
        by_cases hkk : k < sint.nat n
        · exact hall k hk hkk
        · have hkeq : k = sint.nat n := by omega
          have e : tl[k] = tl[sint.nat n]'Hlt' := by simp only [hkeq]
          rw [e, ← hrel.1, ← hrel.2]; exact hno
  · -- not found: `RecordedIn` is false
    try wp_auto
    have hnx : sint.nat n = tl.length := by rw [← hgl, Hgsl.1]; word
    have hany : (tl.any fun p => decide (p.1 ≤ sint.Z t) && decide (p.2 ≥ sint.Z c)) = false := by
      rw [List.any_eq_false]
      intro q hq
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      have := hall k hk (by omega)
      simpa using this
    rw [hany] at Hb
    simp at Hb
    subst Hb
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
