/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.OldVotes` (B 708).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OldVotes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__idx
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__EffTerm
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.OldVotes.wp_proof
    (wp_idx : State.idx.spec (GF := GF) (hG := hG))
    (wp_EffTerm : State.EffTerm.spec (GF := GF) (hG := hG)) :
    State.OldVotes.spec (GF := GF) (hG := hG) := by
  intro p s vs
  wp_start as ⟨#Hs, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  ihave #Hv := HVotes
  iunfold votesRO at Hv
  icases Hv with ⟨%items, #Hitems, %Hrel⟩
  ihave %Hil := ownSlice_len $$ Hitems
  have Hl := Hrel.length_eq
  rw [State.oldVotes, W6Laws.filterM_eq] at Ho
  iapply wp_fupd
  wp_auto
  have hvl : sint.nat g.Votes'.len = items.length := by rw [Hil.1]
  ihave #Hnil := ownSlice_nil (V := G.VoteRec) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.VoteRec) (GF := GF)
  ihave IH : iprop(∃ (k : w64) (vv : G.VoteRec) (osl : GoSlice) (L : List G.VoteRec) (acc : List VoteRec),
      "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap G.VoteRec osl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z g.Votes'.len ∧ List.Forall₂ voteRel L acc ∧
        (s.votes.drop (sint.nat k)).foldlM (W6Laws.fstep (fun v => do
          let __do_lift ← s.idx v.voter
          Pure.pure (decide (s.effTerm __do_lift > v.term)))) acc = .ok vs⌝) $$ [i v out Hcap0]
  · iexists _, _, slice.nil, [], []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    exact ⟨Int.le_refl _, Hil.2, .nil, by rw [show sint.nat (W64 0) = 0 from rfl]; simpa using Ho⟩
  wp_for IH
  obtain ⟨hk0, hk1, hkL, hkS⟩ := Hk
  wp_if_destruct
  · have Hlt' : sint.nat k < items.length := by rw [← hvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
    have Hltv : sint.nat k < s.votes.length := by omega
    obtain ⟨z, Hz⟩ : ∃ z, items[sint.nat k]? = some z := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have hrz : voteRel z s.votes[sint.nat k] := by
      have := forall₂_getElem Hrel (sint.nat k) Hlt' Hltv
      rw [List.getElem?_eq_getElem Hlt'] at Hz; cases Hz; exact this
    obtain ⟨c, hc, hkS⟩ := W6Laws.fold_step Hltv hkS
    obtain ⟨j, hj, hc⟩ := bind_ok hc
    simp only [pure_ok, Except.ok.injEq] at hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z g.Votes'.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index g.Votes' (sint.Z k) items DFrac.discard z hk0 $$ [Hitems] as -
    · isplitr
      · iexact Hitems
      ipureintro; rw [show (sint.Z k).toNat = sint.nat k by rfl]; exact Hz
    try wp_auto
    wp_apply wp_idx p s z.Voter' j $$ [Hs] as %w %Hw
    · iframe Hs; ipureintro; rw [hrz.1]; exact hj
    try wp_auto
    wp_apply wp_EffTerm p s w $$ [Hs] as %u %Hu
    · iframe Hs; ipureintro; omega
    try wp_auto
    have hwn : sint.nat w = j := by have := sint_nat_cast (k := w) (by omega); omega
    have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := sint_add_one_lt Hif; have := sint_nat_cast hk0
      have := sint_nat_cast (k := k + W64 1) (by omega); omega
    have hk' := sint_add_one_lt Hif
    rw [Hu, hrz.2.1, hwn]
    by_cases hz : s.effTerm j > s.votes[sint.nat k].term
    · rw [decide_eq_true hz]
      rw [decide_eq_true hz] at hc
      subst hc
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _, _
      iframe
      ipureintro
      refine ⟨by omega, by omega, W6Laws.forall₂_append_one hkL hrz, ?_⟩
      rw [hk1']; simpa using hkS
    · rw [decide_eq_false hz]
      rw [decide_eq_false hz] at hc
      subst hc
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _, _
      iframe
      ipureintro
      refine ⟨by omega, by omega, hkL, ?_⟩
      rw [hk1']; simpa using hkS
  have hkn : sint.nat k = s.votes.length := by
    rw [← Hl, ← hvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
  rw [hkn] at hkS
  have hacc := W6Laws.fold_end hkS
  subst hacc
  try wp_auto
  imod ownSlice_persist $$ Hout with #Hout
  imodintro
  iapply HΦ
  iunfold votesRO
  iexists _
  iframe Hout
  ipureintro; exact hkL

end proof

end AntCheck
end EtcdGrove
end Perennial
