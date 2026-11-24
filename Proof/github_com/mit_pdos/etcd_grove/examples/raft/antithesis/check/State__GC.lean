/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.GC` (B 713-723).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__GC
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Garbage
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OldVotes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__StaleLed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Over
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Without
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs__Without
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Without
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

theorem State.GC.wp_proof
    (wp_Garbage : State.Garbage.spec (GF := GF) (hG := hG))
    (wp_OldVotes : State.OldVotes.spec (GF := GF) (hG := hG))
    (wp_StaleLed : State.StaleLed.spec (GF := GF) (hG := hG))
    (wp_Over : State.Over.spec (GF := GF) (hG := hG))
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_factsMinus : factsMinus.spec (GF := GF) (hG := hG))
    (wp_votesMinus : votesMinus.spec (GF := GF) (hG := hG))
    (wp_LogsWithout : TermLogs.Without.spec (GF := GF) (hG := hG))
    (wp_ConfsWithout : TermConfs.Without.spec (GF := GF) (hG := hG))
    (wp_IntsWithout : TermInts.Without.spec (GF := GF) (hG := hG)) :
    State.GC.spec (GF := GF) (hG := hG) := by
  intro p s s'
  wp_start as ⟨#Hs, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  unfold State.gc at Ho
  obtain ⟨gs, hgs, Ho⟩ := bind_ok Ho
  obtain ⟨vs, hvs, Ho⟩ := bind_ok Ho
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho
  iapply wp_fupd
  wp_auto
  wp_apply wp_StaleLed p s $$ [Hs] as %ssl #Hss
  · iexact Hs
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  wp_apply wp_Garbage p s gs $$ [Hs] as %gsl #Hgs
  · iframe Hs; ipureintro; exact hgs
  try wp_auto
  wp_apply wp_factsMinus g.Msgs' s.msgs gsl gs $$ [HMsgs Hgs] as %msl #Hms
  · iframe HMsgs Hgs
  try wp_auto
  wp_apply wp_set_msgs q s msl _ $$ [Hq Hms] as Hq
  · iframe Hq Hms
  generalize hs1 : ({ s with msgs := lset.minus s.msgs gs } : State) = s1
  try wp_auto
  wp_apply wp_OldVotes p s vs $$ [Hs] as %vsl #Hvs
  · iframe Hs; ipureintro; exact hvs
  try wp_auto
  wp_apply wp_votesMinus g.Votes' s.votes vsl vs $$ [HVotes Hvs] as %vml #Hvm
  · iframe HVotes Hvs
  try wp_auto
  wp_apply wp_set_votes q s1 vml _ $$ [Hq Hvm] as Hq
  · iframe Hq Hvm
  generalize hs2 : ({ s1 with votes := lset.minus s.votes vs } : State) = s2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_Without_unfold.method_unfold]
  try wp_auto
  wp_apply wp_LogsWithout g.LedLog' s.ledLog ssl s.staleLed $$ [HLedLog Hss] as %lls #Hlls
  · iframe HLedLog Hss
  try wp_auto
  wp_apply wp_set_ledLog q s2 lls _ $$ [Hq Hlls] as Hq
  · iframe Hq Hlls
  generalize hs3 : ({ s2 with ledLog := s.ledLog.without s.staleLed } : State) = s3
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs.TypeAssumptions.ptr_Without_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ConfsWithout g.LedConf' s.ledConf ssl s.staleLed $$ [HLedConf Hss] as %lcs #Hlcs
  · iframe HLedConf Hss
  try wp_auto
  wp_apply wp_set_ledConf q s3 lcs _ $$ [Hq Hlcs] as Hq
  · iframe Hq Hlcs
  generalize hs4 : ({ s3 with ledConf := s.ledConf.without s.staleLed } : State) = s4
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_Without_unfold.method_unfold]
  try wp_auto
  wp_apply wp_IntsWithout g.LedAt' s.ledAt ssl s.staleLed $$ [HLedAt Hss] as %las #Hlas
  · iframe HLedAt Hss
  try wp_auto
  wp_apply wp_set_ledAt q s4 las _ $$ [Hq Hlas] as Hq
  · iframe Hq Hlas
  generalize hs5 : ({ s4 with ledAt := s.ledAt.without s.staleLed } : State) = s5
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_Without_unfold.method_unfold]
  try wp_auto
  wp_apply wp_IntsWithout g.ElAt' s.elAt ssl s.staleLed $$ [HElAt Hss] as %eas #Heas
  · iframe HElAt Hss
  try wp_auto
  wp_apply wp_set_elAt q s5 eas _ $$ [Hq Heas] as Hq
  · iframe Hq Heas
  generalize hs6 : ({ s5 with elAt := s.elAt.without s.staleLed } : State) = s6
  try wp_auto
  ihave #Hlv := HLeaders
  iunfold leadersRO at Hlv
  icases Hlv with ⟨%items, #Hitems, %Hrel⟩
  ihave %Hil := ownSlice_len $$ Hitems
  have Hl := Hrel.length_eq
  have hvl : sint.nat g.Leaders'.len = items.length := by rw [Hil.1]
  ihave #Hnil := ownSlice_nil (V := G.LeaderRec) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.LeaderRec) (GF := GF)
  ihave IH : iprop(∃ (k : w64) (vv : G.LeaderRec) (osl : GoSlice) (L : List G.LeaderRec),
      "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ vv ∗ "ld" ∷ ld_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap G.LeaderRec osl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z g.Leaders'.len ∧
        List.Forall₂ (fun (g : G.LeaderRec) (l : LeaderRec) => g.Server' = l.server ∧ sint.Z g.Term' = l.term) L
          ((s.leaders.take (sint.nat k)).filter (fun l => !s.over l.term))⌝) $$ [i l ld Hcap0]
  · iexists _, _, slice.nil, []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    exact ⟨Int.le_refl _, Hil.2, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hk0, hk1, hkL⟩ := Hk
  wp_if_destruct
  · have Hlt' : sint.nat k < items.length := by rw [← hvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
    have Hltv : sint.nat k < s.leaders.length := by omega
    obtain ⟨z, Hz⟩ : ∃ z, items[sint.nat k]? = some z := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have hrz : z.Server' = s.leaders[sint.nat k].server ∧ sint.Z z.Term' = s.leaders[sint.nat k].term := by
      have := forall₂_getElem Hrel (sint.nat k) Hlt' Hltv
      rw [List.getElem?_eq_getElem Hlt'] at Hz; cases Hz; exact this
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z g.Leaders'.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index g.Leaders' (sint.Z k) items DFrac.discard z hk0 $$ [Hitems] as -
    · isplitr
      · iexact Hitems
      ipureintro; rw [show (sint.Z k).toNat = sint.nat k by rfl]; exact Hz
    try wp_auto
    have hk' := sint_add_one_lt Hif
    have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := sint_nat_cast hk0
      have := sint_nat_cast (k := k + W64 1) (by omega); omega
    have htake : s.leaders.take (sint.nat (k + W64 1)) = s.leaders.take (sint.nat k) ++ [s.leaders[sint.nat k]] := by
      rw [hk1', List.take_add_one, List.getElem?_eq_getElem Hltv]; simp
    have Hnext : 0 ≤ sint.Z (k + W64 1) ∧ sint.Z (k + W64 1) ≤ sint.Z g.Leaders'.len := ⟨by omega, by omega⟩
    wp_apply wp_Over p s z.Term' $$ [Hs]
    · iexact Hs
    rw [hrz.2]
    cases hy : s.over s.leaders[sint.nat k].term
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨Hnext.1, Hnext.2, ?_⟩
      rw [htake, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, hy, Bool.not_false, ite_true]
      exact List.Forall₂.append hkL (List.Forall₂.cons hrz List.Forall₂.nil)
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨Hnext.1, Hnext.2, ?_⟩
      rw [htake, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, hy, Bool.not_true, Bool.false_eq_true, ite_false, List.append_nil]
      exact hkL
  have hkx : sint.nat k = s.leaders.length := by rw [← Hl, ← hvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
  rw [hkx, List.take_length] at hkL
  try wp_auto
  imod ownSlice_persist $$ Hout with #Hout
  ihave #Hld : leadersRO osl (s.leaders.filter (fun l => !s.over l.term)) $$ [Hout]
  · iunfold leadersRO; iexists _; iframe Hout; ipureintro; exact hkL
  wp_apply wp_set_leaders q s6 osl _ $$ [Hq Hld] as Hq
  · iframe Hq Hld
  try wp_auto
  subst hs6 hs5 hs4 hs3 hs2 hs1
  imodintro
  iapply HΦ
  iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
