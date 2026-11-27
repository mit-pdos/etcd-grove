/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__requestVote.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).requestVote`: the protocol steps `setTerm` (at the `currentTerm` store,
on a newer term) and `grantVote` (at `persistVote`), or `vote_again` for a repeated grant.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__requestVote
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
/-- Respond (no grant) and give the main goroutine's resources back at state `s'`, `st'`, with
the stable store `sst'` (`hvm`: its vote matches; `hpost`: the state/term condition). -/
macro "rv_fail" s':term:max st':term:max sst':term:max hvm:term:max hpost:term:max : tactic => `(tactic| (
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp] as rpc
    · iframe rpc Hbag
      iapply rvRespP_intro
      iframe Hrsp Hrvt
      isplitr; · ileft; ipureintro; exact Hrv.2.1
      isplitr; · iexists []; rw [Hrv.2.2]; iapply ownSlice_nil
      rw [Hrv.1]; unfold hdrOk; iexact Hh0
    iapply HΦ
    iexists $s', $st'
    iframe Htok
    isplitl
    · ihave Hmo := mainOwnAt_intro' r γ rc i $s' $st' a $sst' cfg ccfg cidx mli lch γl bs cmp $hvm Ha Hcmp Hccfg Hcap
        $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
      · iframe; iframe Hcfg Hccf Hcmt Hlch Hlchan
      unfold mainOwnAt
      iexact Hmo
    ipureintro; exact $hpost))

set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.Raft.requestVote.wp_proof
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_inConfiguration : github_com.hashicorp.raft.inConfiguration.spec (GF := GF) (hG := hG))
    (wp_LeaderWithID : github_com.hashicorp.raft.Raft.LeaderWithID.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_hasVote : github_com.hashicorp.raft.hasVote.spec (GF := GF) (hG := hG))
    (wp_Equal : bytes.Equal.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_persistVote : github_com.hashicorp.raft.Raft.persistVote.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.Raft.setLastContact.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.requestVote.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc p rq c T li lt γc s st tid => by
  wp_start as ⟨#Hr, Hm, Htok, Hp, Hreq, #Hbag⟩
  unfold mainOwnAt
  icases Hm with ⟨%a, %sst, %cfg, %ccfg, %cidx, %mli, %lch, %γl, %bs, %cmp, Hs, Hdv, HS, %Hvm, Hll, Hst, Hstl,
    Hpend, Hvreg, Happ, %Ha, Hprod, Hpnd, Hcomp, %Hcmp, Hcfgs, #Hcfg, #Hccf, %Hccfg, #Hcmt, #Hlch, #Hlchan, Hlown, %Hcap⟩
  icases cfgAtIs_srvs γ s.log _ cfg $$ Hcfg with ⟨%ss, #Hss, %Hsok⟩
  unfold rvReq
  icases Hreq with ⟨⟨%HTe, %Hlie, %Hlte⟩, #Hhdr, #Hcand, #Hci⟩
  ihave ⟨#HI, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  ipersist Hp
  iStructNamed Hp
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_observe r γ rc i s _ tid $$ [$Hr $Htok] as ⟨-, Htok⟩
  · iapply obsArg_other γ i s _ (mkOk_ne_leaderObs _ _ (by unfold RequestVoteRequest.ty RaftState.ty; simp))
      (mkOk_not_raftState _ _ (by unfold RequestVoteRequest.ty RaftState.ty; simp))
  wp_apply wp_getRPCHeader r γ rc i $$ [$Hr] as %h0 #Hh0
  wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
  irename «$r0» => Hrsp
  imod termLb_of_srv γ r i s $$ [$HI $Htc $Hs] with ⟨Hs, #Htlb0⟩
  imod srvOwn_facts γ ⊤ (by simp) i s $$ [$HI $Hs] with ⟨Hs, -, %Hsf⟩
  have Hst62 : s.term < 2 ^ 62 := Hsf.2.2.2.2.2.1
  ihave Hrsp : (∃ rv : RequestVoteResponse, «$r0_ptr» ↦ rv ∗
      ⌜rv.RPCHeader' = h0 ∧ rv.Granted' = false ∧ rv.Peers' = slice.nil⌝ ∗ termOk γ (uint.nat rv.Term')) $$ [Hrsp]
  · iexists _; iframe Hrsp; isplitr; · ipureintro; exact ⟨rfl, rfl, rfl⟩
    iapply termOk_of_termLb γ i _ s.term (by word) $$ [$Hvi $Htlb0]
  icases Hrsp with ⟨%rv, Hrsp, %Hrv, #Hrvt⟩
  ipersist r
  ipersist resp
  ipersist req
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, -, -, -, -, -⟩
  wp_auto
  iStructNamed RPCHeader
  ihave ⟨%xtr, %rpcCh, #Htr, #Hrpcf, #Htrans⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport
  icases Htrans with ⟨-, -, -, -, #Hdec, -⟩
  unfold hdrOk
  icases Hhdr with ⟨%Hpvr, #Hid, #Haddr⟩
  rename_i candidate_ptr candidateBytes_ptr
  wp_auto
  wp_join iprop(∃ (cs : ServerAddress) (cb : GoSlice), candidate_ptr ↦ cs ∗ candidateBytes_ptr ↦ cb ∗
      ⌜(cs : List w8) = c⌝ ∗ cb ↦*□ c) with [candidate candidateBytes]
    as ⟨%cs, %cb, candidate, candidateBytes, %Hcs, #Hcb⟩
  · wp_apply Hdec $$ Haddr
    iintro -
    wp_auto
    wp_join_done
    iexists _, _
    iframe
    iframe Haddr
    ipureintro; rfl
  · wp_apply Hdec $$ Hcand
    iintro -
    wp_auto
    wp_join_done
    iexists _, _
    iframe
    iframe Hcand
    ipureintro; rfl
  ipersist candidate
  ipersist candidateBytes
  -- (1) a candidate outside the configuration
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg mli))
    at next with [Hcfgs]
  · wp_if_destruct
    · wp_apply wp_bytes_to_string $$ Hid as -
      wp_if_destruct
      · wp_apply wp_inConfiguration cfg ss DFrac.discard _ $$ [$Hss] as -
        wp_if_destruct
        · q_any
        · q_any
      · q_any
    · q_any
  rename_i v1
  iintro ⟨Hv1, Hcfgs⟩
  icases Hv1 with (%Hv1 | %Hv1)
  rotate_left
  · subst Hv1
    wp_auto
    rv_fail s st sst Hvm (Or.inr ⟨rfl, rfl, rfl⟩)
  subst Hv1
  wp_auto
  -- (2) a known leader other than the candidate
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗ rtok tid))
    at next with [Htok]
  · wp_apply wp_LeaderWithID r γ rc i tid $$ [$Hr $Htok] as %la %lid Htok
    repeat' wp_if_destruct
    all_goals (try (cases rq.LeadershipTransfer' <;> wp_auto))
    all_goals q_any
  rename_i v2
  iintro ⟨Hv2, Htok⟩
  icases Hv2 with (%Hv2 | %Hv2)
  rotate_left
  · subst Hv2
    wp_auto
    rv_fail s st sst Hvm (Or.inr ⟨rfl, rfl, rfl⟩)
  subst Hv2
  wp_auto
  -- (3) an older term
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ⌜s.term ≤ T⌝ ∨ ⌜v = returnVal #()⌝) ∗ srvOwn γ i s))
    at next with [Hs]
  · wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
    wp_if_destruct
    · iframe; iright; ipureintro; first | rfl | trivial
    · iframe; ileft; isplitr; · ipureintro; first | rfl | trivial
      ipureintro; rw [← HTe]; have : uint.Z (W64 (s.term : Int)) = s.term := by word
      simp only [uint.nat]; word
  rename_i v3
  iintro ⟨Hv3, Hs⟩
  icases Hv3 with (⟨%Hv3, %HT⟩ | %Hv3)
  rotate_left
  · subst Hv3
    wp_auto
    rv_fail s st sst Hvm (Or.inr ⟨rfl, rfl, rfl⟩)
  subst Hv3
  wp_auto
  -- (4) a newer term: become a follower of it
  wp_join iprop(∃ (s1 : SState) (st1 : w32) (sst1 : StableAbs) (rv1 : RequestVoteResponse),
      srvOwn γ i s1 ∗ ⌜s1 = { s with term := T }⌝ ∗ ghostVar rc.names.state (1 : Qp).half st1 ∗
      (⌜st1 ≠ stLeader⌝ ∨ leaderIs γ s1.term i ∗ (∃ m : Nat, pubOwn γ i s1.term m ∗ ⌜m ≤ a⌝) ∗
        ccfgOwn γ i s1.term (lastCfgIdx s1.log) ∗
        ∃ n0 : Nat, len0Is γ s1.term n0 ∗
          (⌜s1.cidx ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s1.term k p ∗ ⌜s1.cidx ≤ k⌝) ∗
          (⌜cidx ≠ mli ∨ uint.nat mli ≤ n0⌝ ∨ ∃ k p : Nat, commitIs γ s1.term k p ∗ ⌜uint.nat mli ≤ k⌝)) ∗ ⌜st1 = stFollower ∨ (st1 = st ∧ s1 = s)⌝ ∗
      rc.ownS sst1 ∗ ⌜voteMatches sst1 s1⌝ ∗ «$r0_ptr» ↦ rv1 ∗
      ⌜rv1.RPCHeader' = h0 ∧ rv1.Granted' = false ∧ rv1.Peers' = slice.nil⌝ ∗
      termOk γ (uint.nat rv1.Term') ∗ termLb γ i T ∗ rtok tid)
    at next with [Hs Hst Hstl HS Hrsp Htok]
    as ⟨%s1, %st1, %sst1, %rv1, Hs, %Hs1, Hst, Hstl, %Hst1, HS, %Hvm1, Hrsp, %Hrv1, #Hrvt1, #HtlbT, Htok⟩
  · wp_apply wp_getCurrentTerm.1 r γ i s $$ [$HI $Htc $Hs] as Hs
    wp_if_destruct
    · rw [show (Follower : val) = #stFollower from rfl]
      wp_apply wp_setState r γ rc i _ stFollower s $$ [$Hr $Hst $Htok] as ⟨Hst, -, Htok⟩
      · isplitr; · ipureintro; left; rfl
        iapply obsArg_state γ i s stFollower (by decide)
      ihave #HokT := termOk_of_candIs γ c T li lt $$ Hci
      ihave Hupd := setTerm_step γ i s T HT $$ [$HI $Hs $HokT]
      wp_apply wp_setCurrentTerm r γ rc i sst rq.Term'
        iprop(srvOwn γ i { s with term := T } ∗ termLb γ i T) $$ [$Hr $HS Hupd] as ⟨HS, Hs, #HtlbT⟩
      · rw [HTe]; iexact Hupd
      wp_join_done
      iexists _, stFollower, _, { rv with Term' := rq.Term' }
      iframe
      rw [HTe]
      iframe HtlbT
      isplitr; · ipureintro; rfl
      isplitr; · ileft; ipureintro; decide
      isplitr; · ipureintro; left; rfl
      isplitr; · ipureintro; exact voteMatches_term sst s rq.Term' T Hvm
      isplitr; · ipureintro; exact Hrv
      iapply termOk_of_termLb γ i T T (Nat.le_refl _) $$ [$Hvi $HtlbT]
    · have HTs : T = s.term := by
        rw [← HTe]; have : uint.Z (W64 (s.term : Int)) = s.term := by word
        simp only [uint.nat]; word
      have Hss : { s with term := T } = s := by rw [HTs]
      wp_join_done
      iexists s, st, sst, rv
      iframe
      rw [HTs]
      iframe Htlb0 Hrvt
      ipureintro
      exact ⟨rfl, Or.inr ⟨rfl, rfl⟩, Hvm, Hrv⟩
  subst Hs1
  ihave #HcmtT := cmtIdx_mono γ s.term T s.log s.log (uint.nat cidx) HT rfl $$ Hcmt
  iclear Hcmt
  irename HcmtT => Hcmt
  have Hrv := Hrv1
  iclear Hrvt
  irename Hrvt1 => Hrvt
  have Hpost1 : st1 = stFollower ∨ (st1 = st ∧ ({ s with term := T } : SState).term = s.term ∧
      ({ s with term := T } : SState).log = s.log) := by
    rcases Hst1 with h | ⟨h1, h2⟩
    · left; exact h
    · right; refine ⟨h1, ?_, rfl⟩; rw [h2]
  -- (5) a candidate without a vote
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∨ ⌜v = returnVal #()⌝) ∗
        r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg mli))
    at next with [Hcfgs]
  · wp_if_destruct
    · wp_apply wp_bytes_to_string $$ Hid as -
      wp_if_destruct
      · wp_apply wp_hasVote cfg ss DFrac.discard _ $$ [$Hss] as -
        · ipureintro; exact Hsok.2.2
        wp_if_destruct
        · q_any
        · q_any
      · q_any
    · q_any
  rename_i v5
  iintro ⟨Hv5, Hcfgs⟩
  icases Hv5 with (%Hv5 | %Hv5)
  rotate_left
  · subst Hv5
    wp_auto
    rv_fail { s with term := T } st1 sst1 Hvm1 Hpost1
  subst Hv5
  wp_auto
  -- the stable store's last vote
  ihave #Hg := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hg with ⟨-, -, ⟨%k1, #Hk1, #Hk1s⟩, ⟨%k2, #Hk2, #Hk2s⟩, -⟩
  ihave ⟨%xst, #Hstf, #Hss⟩ := isRaft_stableStore r γ rc i $$ Hr
  unfold isStableStore
  icases Hss with ⟨#HgetU, #HsetU, #Hget, #Hset⟩
  wp_auto
  wp_apply_core HgetU $$ HS Hk1s Htok
  iintro HS Htok
  wp_auto
  wp_join (Q := fun v => iprop(∃ (sl : GoSlice) (err : GoInterface), ⌜v = PairV #sl #err⌝ ∗
      rc.ownS sst1 ∗ rtok tid ∗
      ((⌜err = interface.nil⌝ ∗ ∃ vb, ⌜sst1.bytes.lookup (go!"LastVoteCand" : List w8) = some vb⌝ ∗ sl ↦*□ vb) ∨
       (isNotFoundErr err ∗ ⌜sl = Perennial.zero_val GoSlice ∧
          ∀ vb, sst1.bytes.lookup (go!"LastVoteCand" : List w8) = some vb → vb = []⌝))))
    at (#(methods _ _ _) _) with [HS Htok]
  · wp_apply_core Hget $$ HS Hk2s Htok
    iintro HS Htok
    isplit
    · iintro %vb %hvb %sl #Hsl
      iexists sl, interface.nil
      iframe
      isplitr; · ipureintro; rfl
      ileft; isplitr; · ipureintro; rfl
      iexists vb; iframe Hsl; ipureintro; exact hvb
    · iintro %hnone %err Herr
      iexists _, err
      iframe
      isplitr; · ipureintro; rfl
      iright; iframe Herr; ipureintro; exact ⟨rfl, hnone⟩
  rename_i v6
  iintro ⟨%sl, %err, %Hv6, HS, Htok, Hgp⟩
  subst Hv6
  wp_auto
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∗
      ((⌜err = interface.nil⌝ ∗ ∃ vb, ⌜sst1.bytes.lookup (go!"LastVoteCand" : List w8) = some vb⌝ ∗ sl ↦*□ vb) ∨
       (⌜sl = Perennial.zero_val GoSlice ∧
          ∀ vb, sst1.bytes.lookup (go!"LastVoteCand" : List w8) = some vb → vb = []⌝))))
    at next with [Hgp err]
  · icases Hgp with (⟨%He, Hvb⟩ | ⟨Hnf, %Hsl⟩)
    · subst He
      wp_auto
      isplitr; · ipureintro; first | rfl | trivial
      ileft; iframe; ipureintro; rfl
    · unfold isNotFoundErr
      icases Hnf with ⟨%pe, %Hpe, #Hpe⟩
      subst Hpe
      iStructNamed Hpe
      iclear Hdec HgetU HsetU Hget Hset
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      isplitr; · ipureintro; first | rfl | trivial
      iright; ipureintro; exact Hsl
  rename_i v7
  iintro ⟨%Hv7, Hgp⟩
  subst Hv7
  wp_auto
  imod srvOwn_facts γ ⊤ (by simp) i _ $$ [$HI $Hs] with ⟨Hs, -, %Hsf1⟩
  imod srvOwn_vcand γ ⊤ (by simp) i _ $$ [$HI $Hs] with ⟨Hs, %Hvc⟩
  imod srvs_ne_nil γ ⊤ (by simp) $$ HI with %Hss1
  imod candIs_pos γ ⊤ (by simp) c T li lt $$ [$HI $Hci] with %HT1
  have Hvt := Hvm1.1
  -- (6) already voted in this term
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ srvOwn γ i { s with term := T } ∗ «$r0_ptr» ↦ rv1 ∗ ⌜s.vterm < T⌝) ∨
      (⌜v = returnVal #()⌝ ∗ srvOwn γ i { s with term := T } ∗ ∃ rvx : RequestVoteResponse,
        «$r0_ptr» ↦ rvx ∗ ⌜rvx.RPCHeader' = h0 ∧ rvx.Peers' = slice.nil ∧ rvx.Term' = rv1.Term'⌝ ∗
        (⌜rvx.Granted' = false⌝ ∨ voteIs γ i T c))))
    at next with [Hs Hrsp Hgp lastVoteCandBytes]
  · wp_if_destruct
    · have hvT : s.vterm = T := by rw [← Hvt, Hif, HTe]
      have hT1 : 1 ≤ T := HT1
      have hne : s.vcand ≠ [] := Hss1 _ (Hvc (by simp; omega))
      have hlk : sst1.bytes.lookup (go!"LastVoteCand" : List w8) = some s.vcand :=
        Hvm1.2.resolve_left (by simp; omega)
      icases Hgp with (⟨%He, %vb, %Hvb, #Hsl⟩ | %Hsl)
      · rw [hlk] at Hvb
        cases Hvb
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        have hsl : sl ≠ slice.nil := by
          intro h; subst h; apply hne
          have : (slice.nil : GoSlice).len = W64 0 := rfl
          rw [this] at Hsll; exact List.eq_nil_of_length_eq_zero (by rw [Hsll.1]; rfl)
        rw [show (!decide (sl = slice.nil)) = true by simp [hsl]]
        wp_auto
        wp_apply wp_Equal sl cb DFrac.discard DFrac.discard s.vcand c $$ [$Hsl $Hcb] as ⟨-, -⟩
        imod vote_again γ ⊤ (by simp) i { s with term := T } (by simp; omega) $$ [$HI $Hs]
          with ⟨Hs, #Hvote⟩
        wp_if_destruct
        · q_ret
          iframe Hs
          iexists _
          iframe Hrsp
          isplitr; · ipureintro; exact ⟨Hrv.1, Hrv.2.2, rfl⟩
          iright
          rw [← hvT, ← Hif]
          iexact Hvote
        · q_ret
          iframe Hs
          iexists _
          iframe Hrsp
          isplitr; · ipureintro; exact ⟨Hrv.1, Hrv.2.2, rfl⟩
          ileft; ipureintro; exact Hrv.2.1
      · exfalso; exact hne (Hsl.2 _ hlk)
    · q_exec
      iframe
      ipureintro
      have h1 : s.vterm ≠ T := by
        intro h; apply Hif
        apply BitVec.eq_of_toNat_eq
        have e1 := Hvt; have e2 := HTe
        simp only [uint.nat] at e1 e2; omega
      have h2 := Hsf1.2.2.2.1
      simp only at h2; omega
  rename_i v8
  iintro (⟨%Hv8, Hs, Hrsp, %Hvlt⟩ | ⟨%Hv8, Hs, %rvx, Hrsp, %Hrvx, Hgr⟩)
  rotate_left
  · subst Hv8
    wp_auto
    wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp Hgr] as rpc
    · iframe rpc Hbag
      iapply rvRespP_intro
      iframe Hrsp Hgr
      rw [Hrvx.2.2]
      iframe Hrvt
      isplitr; · iexists []; rw [Hrvx.2.1]; iapply ownSlice_nil
      rw [Hrvx.1]; unfold hdrOk; iexact Hh0
    iapply HΦ
    iexists { s with term := T }, st1
    iframe Htok
    isplitl
    · ihave Hmo := mainOwnAt_intro' r γ rc i { s with term := T } st1 a sst1 cfg ccfg cidx mli lch γl bs cmp Hvm1
        Ha Hcmp Hccfg Hcap $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
      · iframe; iframe Hcfg Hccf Hcmt Hlch Hlchan
      unfold mainOwnAt
      iexact Hmo
    ipureintro; exact Hpost1
  subst Hv8
  wp_auto
  wp_apply wp_getLastEntry r γ rc i { s with term := T } a $$ [$Hr $Hll $Hs $Happ] as %lx %ly ⟨%Hlxy, Hll, Hs, Happ⟩
  · ipureintro; exact Ha.1
  simp only at Hlxy
  -- (7) the candidate's log must be at least as up to date
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ⌜¬ lt < lastTerm s.log⌝) ∨ ⌜v = returnVal #()⌝))
    at next with []
  · wp_if_destruct
    · iright; ipureintro; first | rfl | trivial
    · ileft; isplitr; · ipureintro; first | rfl | trivial
      ipureintro; have e2 := Hlxy.2; have e3 := Hlte; simp only [uint.nat] at e2 e3 ⊢; word
  rename_i v9
  iintro (⟨%Hv9, %Hup1⟩ | %Hv9)
  rotate_left
  · subst Hv9
    wp_auto
    rv_fail { s with term := T } st1 sst1 Hvm1 Hpost1
  subst Hv9
  wp_auto
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ⌜upToDate li lt s.log⌝) ∨ ⌜v = returnVal #()⌝))
    at next with [lastIdx]
  · repeat' wp_if_destruct
    all_goals (first
      | (iright; ipureintro; first | rfl | trivial)
      | (ileft; isplitr; · ipureintro; first | rfl | trivial
         ipureintro; unfold upToDate
         have e1 := Hlxy.1; have e2 := Hlxy.2; have e3 := Hlte; have e4 := Hlie
         simp only [uint.nat] at e1 e2 e3 e4 Hup1 ⊢
         first | (left; word) | (right; constructor <;> word)))
  rename_i v10
  iintro (⟨%Hv10, %Hup⟩ | %Hv10)
  rotate_left
  · subst Hv10
    wp_auto
    rv_fail { s with term := T } st1 sst1 Hvm1 Hpost1
  subst Hv10
  wp_auto
  -- (8) grant: the protocol step `grantVote` at `persistVote`
  imod grantVote_upd γ ⊤ (by simp) i c { s with term := T } li lt Hvlt Hup $$ [$HI $Hs $Hci]
    with ⟨Hs, #Hvote⟩
  wp_apply wp_persistVote r γ rc i sst1 rq.Term' cb c $$ [$Hr $HS $Hcb] as HS
  have Hvm2 : voteMatches (StableAbs.mk (sst1.ints.insert (go!"LastVoteTerm" : List w8) rq.Term')
      (sst1.bytes.insert (go!"LastVoteCand" : List w8) c))
      { { s with term := T } with vterm := ({ s with term := T } : SState).term, vcand := c } := by
    unfold voteMatches
    simp only [GMap.lookup_insert_eq_iff, if_pos]
    exact ⟨HTe, Or.inr trivial⟩
  wp_apply wp_setLastContact r γ rc i $$ [$Hr]
  wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [rpc Hrsp] as rpc
  · iframe rpc Hbag
    iapply rvRespP_intro
    iframe Hrsp Hrvt
    isplitr; · iright; iexact Hvote
    isplitr; · iexists []; rw [Hrv.2.2]; iapply ownSlice_nil
    rw [Hrv.1]; unfold hdrOk; iexact Hh0
  iapply HΦ
  iexists { { s with term := T } with vterm := ({ s with term := T } : SState).term, vcand := c }, st1
  iframe Htok
  isplitl
  · ihave Hmo := mainOwnAt_intro' r γ rc i
      { { s with term := T } with vterm := ({ s with term := T } : SState).term, vcand := c } st1 a _
      cfg ccfg cidx mli lch γl bs cmp Hvm2 Ha Hcmp Hccfg Hcap $$ [Hs Hdv HS Hll Hst Hstl Happ Hprod Hcfgs Hlown Hpend Hvreg Hpnd Hcomp]
    · iframe; iframe Hcfg Hccf Hcmt Hlch Hlchan
    unfold mainOwnAt
    iexact Hmo
  ipureintro; exact Hpost1
