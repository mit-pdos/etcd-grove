/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__requestPreVote.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).requestPreVote`: no protocol step; the response's term is the
request's or the server's (an existing term).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__requestPreVote
public import Dsverify.Spec.github_com.hashicorp.raft.RequestPreVoteRequest__GetRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeaderWithID
public import Dsverify.Spec.github_com.hashicorp.raft.inConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.hasVote
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__persistVote
public import Dsverify.Proof.github_com.hashicorp.raft.core.ObsHelpers
public import Perennial.Spec.bytes.Equal
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryStageCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processConfigurationLogEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.min
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect
public import Perennial.Spec.sync.atomic.Bool__Load

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

set_option hygiene false in
/-- Respond and give the unchanged resources back. -/
macro "pv_fin" : tactic => `(tactic| (
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp] as rpc
    · iframe rpc Hbag
      iapply pvRespP_intro
      iframe Hrsp Hrvt
      rw [Hrv]; unfold hdrOk; iexact Hh0
    iapply HΦ
    iexists s, st
    iframe Htok
    isplitl
    · ihave Hmo := mainOwnAt_intro' r γ rc i s st a sst cfg ccfg cidx li lch γl bs cmp Hvm Ha Hcmp Hccfg Hcap
        $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
      · iframe; iframe Hcfg Hccf Hcmt Hlch Hlchan
      unfold mainOwnAt
      iexact Hmo
    ipureintro; exact Or.inr ⟨rfl, rfl, rfl⟩))

set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.Raft.requestPreVote.wp_proof
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_pv_hdr : github_com.hashicorp.raft.RequestPreVoteRequest.GetRPCHeader.spec (GF := GF) (hG := hG))
    (wp_inConfiguration : github_com.hashicorp.raft.inConfiguration.spec (GF := GF) (hG := hG))
    (wp_LeaderWithID : github_com.hashicorp.raft.Raft.LeaderWithID.spec (GF := GF) (hG := hG))
    (wp_hasVote : github_com.hashicorp.raft.hasVote.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.requestPreVote.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc p rq c T γc s st tid => by
  wp_start as ⟨#Hr, Hm, Htok, Hp, Hreq, #Hbag⟩
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %li, %lch, %γl, %bs, %cmp, Hs, Hdv, HS, %Hvm, Hll, Hst, Hstl,
    Hpend, Hvreg, Happ, %Ha, Hprod, Hpnd, Hcomp, %Hcmp, Hcfgs, #Hcfg, #Hccf, %Hccfg, #Hcmt, #Hlch, #Hlchan, Hlown, %Hcap⟩
  icases cfgAtIs_srvs γ s.log _ cfg $$ Hcfg with ⟨%ss, #Hss, %Hok⟩
  unfold pvReq
  icases Hreq with ⟨%HTe, #Hhdr⟩
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_observe r γ rc i s _ tid $$ [$Hr $Htok] as ⟨-, Htok⟩
  · iapply obsArg_other γ i s _ (mkOk_ne_leaderObs _ _ (by unfold RequestPreVoteRequest.ty RaftState.ty; simp))
      (mkOk_not_raftState _ _ (by unfold RequestPreVoteRequest.ty RaftState.ty; simp))
  wp_apply wp_getRPCHeader r γ rc i $$ [$Hr] as %h0 #Hh0
  wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
  irename «$r0» => Hrsp
  imod termLb_of_srv γ r i s $$ [$HI $Htc $Hs] with ⟨Hs, #Htlb0⟩
  imod srvOwn_facts γ ⊤ (by simp) i s $$ [$HI $Hs] with ⟨Hs, -, %Hsf⟩
  have Hst62 : s.term < 2 ^ 62 := Hsf.2.2.2.2.2.1
  ihave Hrsp : (∃ rv : RequestPreVoteResponse, «$r0_ptr» ↦ rv ∗ ⌜rv.RPCHeader' = h0⌝ ∗
      (⌜uint.nat rv.Term' = T⌝ ∨ termOk γ (uint.nat rv.Term'))) $$ [Hrsp]
  · iexists _; iframe Hrsp; isplitr; · ipureintro; rfl
    iright; iapply termOk_of_termLb γ i _ s.term (by word) $$ [$Hvi $Htlb0]
  icases Hrsp with ⟨%rv, Hrsp, %Hrv, #Hrvt⟩
  ipersist r
  ipersist resp
  ipersist req
  wp_apply wp_pv_hdr p rq $$ [$Hp] as Hp
  ipersist Hp
  iStructNamed Hp
  iStructNamed RPCHeader
  ihave ⟨%xtr, %rpcCh, #Htr, #Hrpcf, #Htrans⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport
  icases Htrans with ⟨-, -, -, -, #Hdec, -⟩
  unfold hdrOk
  icases Hhdr with ⟨%Hpvr, #Hid, #Haddr⟩
  wp_auto
  wp_apply Hdec $$ Haddr
  iintro -
  wp_auto
  wp_apply wp_bytes_to_string $$ Hid as -
  ipersist candidateID
  ipersist candidate
  -- not in the configuration
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗
      r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li))
    at next with [Hcfgs]
  · repeat' (first | wp_if_destruct | wp_auto | wp_apply wp_inConfiguration cfg ss DFrac.discard _ $$ [$Hss] as -)
    all_goals q_any
  rename_i v1
  iintro ⟨Hv1, Hcfgs⟩
  icases Hv1 with (%Hv1 | %Hv1)
  rotate_left
  · subst Hv1
    wp_auto
    pv_fin
  subst Hv1
  wp_auto
  -- a known leader other than the candidate
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗ rtok tid))
    at next with [Htok]
  · wp_apply wp_LeaderWithID r γ rc i tid $$ [$Hr $Htok] as %la %lid Htok
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals q_any
  rename_i v2
  iintro ⟨Hv2, Htok⟩
  icases Hv2 with (%Hv2 | %Hv2)
  rotate_left
  · subst Hv2
    wp_auto
    pv_fin
  subst Hv2
  wp_auto
  -- an older term
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗ srvOwn γ i s))
    at next with [Hs]
  · wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
    repeat' wp_if_destruct
    all_goals q_any
  rename_i v3
  iintro ⟨Hv3, Hs⟩
  icases Hv3 with (%Hv3 | %Hv3)
  rotate_left
  · subst Hv3
    wp_auto
    pv_fin
  subst Hv3
  wp_auto
  -- a newer term: answer with it
  wp_join iprop(∃ rv1 : RequestPreVoteResponse, «$r0_ptr» ↦ rv1 ∗ ⌜rv1.RPCHeader' = h0⌝ ∗
      (⌜uint.nat rv1.Term' = T⌝ ∨ termOk γ (uint.nat rv1.Term')) ∗ srvOwn γ i s)
    at next with [Hrsp Hs]
    as ⟨%rv1, Hrsp, %Hrv1, #Hrvt1, Hs⟩
  · wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
    wp_if_destruct
    · try wp_join_done
      iexists _; iframe Hrsp Hs; isplitr; · ipureintro; exact Hrv
      ileft; ipureintro; exact HTe
    · try wp_join_done
      iexists _; iframe Hrsp Hrvt Hs; ipureintro; exact Hrv
  have Hrv := Hrv1
  iclear Hrvt
  irename Hrvt1 => Hrvt
  -- a candidate without a vote
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗
      r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li))
    at next with [Hcfgs]
  · repeat' (first | wp_if_destruct | wp_auto | (ipureintro; exact Hok.2.2) | wp_apply wp_hasVote cfg ss DFrac.discard _ $$ [$Hss] as -)
    all_goals q_any
  rename_i v4
  iintro ⟨Hv4, Hcfgs⟩
  icases Hv4 with (%Hv4 | %Hv4)
  rotate_left
  · subst Hv4
    wp_auto
    pv_fin
  subst Hv4
  wp_auto
  wp_apply wp_getLastEntry r γ rc i s a $$ [$Hr $Hll $Hs $Happ] as %lx %ly ⟨%Hlxy, Hll, Hs, Happ⟩
  · ipureintro; exact Ha.1
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝)) at next with []
  · repeat' (first | wp_if_destruct | wp_auto)
    all_goals (first | (ileft; ipureintro; first | rfl | trivial) | (iright; ipureintro; first | rfl | trivial))
  rename_i v5
  iintro %Hv5
  rcases Hv5 with Hv5 | Hv5
  rotate_left
  · subst Hv5
    wp_auto
    pv_fin
  subst Hv5
  wp_auto
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝)) at next with [lastIdx]
  · repeat' (first | wp_if_destruct | wp_auto)
    all_goals (first | (ileft; ipureintro; first | rfl | trivial) | (iright; ipureintro; first | rfl | trivial))
  rename_i v6
  iintro %Hv6
  rcases Hv6 with Hv6 | Hv6
  rotate_left
  · subst Hv6
    wp_auto
    pv_fin
  subst Hv6
  wp_auto
  pv_fin
