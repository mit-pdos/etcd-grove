/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.OneVotePerTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OneVotePerTerm
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

theorem State.OneVotePerTerm_all_take_succ {α : Type} (f : α → Bool) (l : List α) (n : Nat) (x : α)
    (h : l[n]? = some x) : (l.take (n + 1)).all f = ((l.take n).all f && f x) := by
  rw [List.take_add_one, List.all_append, h]
  simp

theorem State.OneVotePerTerm_rel_at {A B : Type} {R : A → B → Prop} {gs : List A} {ls : List B}
    (h : List.Forall₂ R gs ls) (k : Nat) (hk : k < ls.length) :
    ∃ g l, gs[k]? = some g ∧ ls[k]? = some l ∧ R g l := by
  have hl := h.length_eq
  exact ⟨gs[k], ls[k], List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hk,
    forall₂_getElem h k (by omega) hk⟩

/-- The inner test of `OneVotePerTerm`. -/
def State.OneVotePerTerm_Q (a b : VoteRec) : Bool := !(a.voter == b.voter && a.term == b.term && a.cand != b.cand)

/-- The outer test of `OneVotePerTerm`. -/
def State.OneVotePerTerm_P (vs : List VoteRec) (a : VoteRec) : Bool := vs.all (State.OneVotePerTerm_Q a)

theorem State.OneVotePerTerm.wp_proof : State.OneVotePerTerm.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold votesRO at HVotes
  icases HVotes with ⟨%gs, #Hgs, %Hrel⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  have hgl := Hrel.length_eq
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : G.VoteRec),
      "i" ∷ i_ptr ↦ n ∗ "a" ∷ a_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Votes'.len ∧ (s.votes.take (sint.nat n)).all (State.OneVotePerTerm_P s.votes) = true⌝)
      $$ [i a]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt' : sint.nat n < s.votes.length := by clear hnt; rw [← hgl, Hlen.1]; word
    obtain ⟨ga, la, Hy, Hla, hra⟩ := State.OneVotePerTerm_rel_at Hrel _ Hlt'
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hnt; word
    wp_apply wp_load_index g.Votes' n gs _ hn0 Hy $$ [Hgs]
    · iexact Hgs
    try wp_auto
    ihave IJ : iprop(∃ (m : w64) (z : G.VoteRec),
        "i" ∷ i_ptr ↦ m ∗ "b" ∷ b_ptr ↦ z ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z g.Votes'.len ∧
          (s.votes.take (sint.nat m)).all (State.OneVotePerTerm_Q la) = true⌝)
        $$ [i b]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IJ
    obtain ⟨hm0, hm1, hmt⟩ := Hm
    wp_if_destruct
    · have Hlt2' : sint.nat m < s.votes.length := by clear hmt hnt; rw [← hgl, Hlen.1]; word
      obtain ⟨gb, lb, Hy2, Hlb, hrb⟩ := State.OneVotePerTerm_rel_at Hrel _ Hlt2'
      have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hmt hnt; word
      wp_apply wp_load_index g.Votes' m gs _ hm0 Hy2 $$ [Hgs]
      · iexact Hgs
      try wp_auto
      have hstep := State.OneVotePerTerm_all_take_succ (State.OneVotePerTerm_Q la) s.votes (sint.nat m) lb Hlb
      try wp_auto
      by_cases hv : ga.Voter' = gb.Voter'
      · rw [decide_eq_true hv]
        try wp_auto
        by_cases ht : ga.Term' = gb.Term'
        · rw [decide_eq_true ht]
          try wp_auto
          by_cases hc : ga.Cand' = gb.Cand'
          · rw [decide_eq_true hc]
            have hq : State.OneVotePerTerm_Q la lb = true := by
              simp only [State.OneVotePerTerm_Q, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
              right; rw [← hra.2.2, ← hrb.2.2, hc]
            try wp_auto
            wp_for_post
            iframe
            iexists _, _
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [hm1', hstep, hmt, hq]
          · rw [decide_eq_false hc]
            try wp_auto
            wp_for_post
            try wp_auto
            wp_for_post
            try wp_auto
            have hQ : State.OneVotePerTerm_Q la lb = false := by
              simp only [State.OneVotePerTerm_Q, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
              rw [← hra.1, ← hrb.1, ← hra.2.1, ← hrb.2.1, ← hra.2.2, ← hrb.2.2, hv, ht]; exact ⟨⟨rfl, rfl⟩, hc⟩
            have hP : State.OneVotePerTerm_P s.votes la = false := by
              simp only [State.OneVotePerTerm_P, List.all_eq_false]
              exact ⟨lb, List.mem_of_getElem? Hlb, by rw [hQ]; decide⟩
            have : s.oneVotePerTerm = false := by
              unfold State.oneVotePerTerm
              rw [List.all_eq_false]
              exact ⟨la, List.mem_of_getElem? Hla, by rw [show s.votes.all (fun b => !(la.voter == b.voter && la.term == b.term && la.cand != b.cand)) = State.OneVotePerTerm_P s.votes la from rfl, hP]; decide⟩
            rw [this]
            iapply HΦ; ipureintro; trivial
        · rw [decide_eq_false ht]
          have hq : State.OneVotePerTerm_Q la lb = true := by
            simp only [State.OneVotePerTerm_Q, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
            left; right; rw [← hra.2.1, ← hrb.2.1]; intro h; exact ht (BitVec.toInt_inj.mp h)
          try wp_auto
          wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hm1', hstep, hmt, hq]
      · rw [decide_eq_false hv]
        have hq : State.OneVotePerTerm_Q la lb = true := by
          simp only [State.OneVotePerTerm_Q, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
          left; left; rw [← hra.1, ← hrb.1]; exact hv
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hm1', hstep, hmt, hq]
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      have hmx : sint.nat m = s.votes.length := by clear hmt hnt; rw [← hgl, Hlen.1]; word
      rw [hmx, List.take_length] at hmt
      refine ⟨by word, by word, ?_⟩
      rw [hn1', State.OneVotePerTerm_all_take_succ (State.OneVotePerTerm_P s.votes) s.votes (sint.nat n) la Hla, hnt]
      exact hmt
  · have hnx : sint.nat n = s.votes.length := by clear hnt; rw [← hgl, Hlen.1]; word
    rw [hnx, List.take_length] at hnt
    have : s.oneVotePerTerm = true := hnt
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
