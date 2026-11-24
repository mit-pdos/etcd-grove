/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.ElectionSafety`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ElectionSafety
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem State.ElectionSafety_all_take_succ {α : Type} (f : α → Bool) (l : List α) (n : Nat) (x : α)
    (h : l[n]? = some x) : (l.take (n + 1)).all f = ((l.take n).all f && f x) := by
  rw [List.take_add_one, List.all_append, h]
  simp

theorem State.ElectionSafety_rel_at {A B : Type} {R : A → B → Prop} {gs : List A} {ls : List B}
    (h : List.Forall₂ R gs ls) (k : Nat) (hk : k < ls.length) :
    ∃ g l, gs[k]? = some g ∧ ls[k]? = some l ∧ R g l := by
  have hl := h.length_eq
  exact ⟨gs[k], ls[k], List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hk,
    forall₂_getElem h k (by omega) hk⟩

theorem State.ElectionSafety.wp_proof : State.ElectionSafety.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold leadersRO at HLeaders
  icases HLeaders with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have hgl := Hrel.length_eq
  let Q : LeaderRec → LeaderRec → Bool := fun a b => !(a.term == b.term && a.server != b.server)
  let P : LeaderRec → Bool := fun a => s.leaders.all (Q a)
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : G.LeaderRec),
      "i" ∷ i_ptr ↦ n ∗ "a" ∷ a_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Leaders'.len ∧ (s.leaders.take (sint.nat n)).all P = true⌝)
      $$ [i a]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt' : sint.nat n < s.leaders.length := by clear hnt; rw [← hgl, Hlen.1]; word
    obtain ⟨ga, la, Hy, Hla, hra⟩ := State.ElectionSafety_rel_at Hrel _ Hlt'
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hnt; word
    wp_apply wp_load_index g.Leaders' n gs _ hn0 Hy $$ [Hgs]
    · iexact Hgs
    try wp_auto
    ihave IJ : iprop(∃ (m : w64) (z : G.LeaderRec),
        "i" ∷ i_ptr ↦ m ∗ "b" ∷ b_ptr ↦ z ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z g.Leaders'.len ∧
          (s.leaders.take (sint.nat m)).all (Q la) = true⌝)
        $$ [i b]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IJ
    obtain ⟨hm0, hm1, hmt⟩ := Hm
    wp_if_destruct
    · have Hlt2' : sint.nat m < s.leaders.length := by clear hmt hnt; rw [← hgl, Hlen.1]; word
      obtain ⟨gb, lb, Hy2, Hlb, hrb⟩ := State.ElectionSafety_rel_at Hrel _ Hlt2'
      have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hmt hnt; word
      wp_apply wp_load_index g.Leaders' m gs _ hm0 Hy2 $$ [Hgs]
      · iexact Hgs
      try wp_auto
      have hstep := State.ElectionSafety_all_take_succ (Q la) s.leaders (sint.nat m) lb Hlb
      by_cases ht : ga.Term' = gb.Term'
      · rw [decide_eq_true ht]
        try wp_auto
        by_cases hsv : ga.Server' = gb.Server'
        · rw [decide_eq_true hsv]
          try wp_auto
          wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hm1', hstep, hmt]
          simp only [Q, Bool.true_and, Bool.not_eq_true', Bool.and_eq_false_iff, bne_eq_false_iff_eq]
          right; rw [← hra.1, ← hrb.1, hsv]
        · rw [decide_eq_false hsv]
          try wp_auto
          wp_for_post
          try wp_auto
          wp_for_post
          try wp_auto
          have hQ : Q la lb = false := by
            simp only [Q, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
            rw [← hra.1, ← hrb.1, ← hra.2, ← hrb.2, ht]; exact ⟨rfl, hsv⟩
          have hP : P la = false := by
            simp only [P, List.all_eq_false]
            exact ⟨lb, List.mem_of_getElem? Hlb, by rw [hQ]; decide⟩
          have : s.electionSafety = false := by
            unfold State.electionSafety
            rw [List.all_eq_false]
            exact ⟨la, List.mem_of_getElem? Hla, by rw [show s.leaders.all (fun b => !(la.term == b.term && la.server != b.server)) = P la from rfl, hP]; decide⟩
          rw [this]
          iapply HΦ; ipureintro; trivial
      · rw [decide_eq_false ht]
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hm1', hstep, hmt]
        simp only [Q, Bool.true_and, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        left; rw [← hra.2, ← hrb.2]; intro h; apply ht; word
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      have hmx : sint.nat m = s.leaders.length := by clear hmt hnt; rw [← hgl, Hlen.1]; word
      rw [hmx, List.take_length] at hmt
      refine ⟨by word, by word, ?_⟩
      rw [hn1', State.ElectionSafety_all_take_succ P s.leaders (sint.nat n) la Hla, hnt]
      exact hmt
  · have hnx : sint.nat n = s.leaders.length := by clear hnt; rw [← hgl, Hlen.1]; word
    rw [hnx, List.take_length] at hnt
    have : s.electionSafety = true := hnt
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
