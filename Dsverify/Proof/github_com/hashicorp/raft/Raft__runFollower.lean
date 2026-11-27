/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__runFollower.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).runFollower`: the follower loop. Its select has thirteen clauses: the RPC
channel (`processRPC`), `applyCh` (answered `ErrNotLeader`), the heartbeat timer (on a timeout, the
server becomes candidate), and channels that are never sent on (their clauses are vacuous; in
particular `bootstrapCh`, so `liveBootstrap` is unreachable from here).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runFollower
public import Dsverify.Proof.github_com.hashicorp.raft.main.Respond
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processRPC
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LastContact
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.hasVote
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.main.CfgReq
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect
public import Perennial.Spec.time.Since

@[expose] public section

set_option linter.deprecated false

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

theorem github_com.hashicorp.raft.Raft.runFollower.wp_proof
    (wp_getState : github_com.hashicorp.raft.raftState.getState.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_randomTimeout : github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG))
    (wp_processRPC : github_com.hashicorp.raft.Raft.processRPC.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG))
    (wp_LastContact : github_com.hashicorp.raft.Raft.LastContact.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_hasVote : github_com.hashicorp.raft.hasVote.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_Clone : github_com.hashicorp.raft.Configuration.Clone.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.runFollower.spec (GF := GF) (hG := hG) :=
  fun r γ rc i tid => by
  wp_start as ⟨#Hr, Hm, Htok⟩
  ihave #Hsc := isRaft_stateCell r γ rc i $$ Hr
  ihave #Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans
  unfold deadField deadChan
  icases Hch with ⟨⟨%applyCh, #HapplyCh, %γa, #Happly⟩, ⟨%vch, #Hvf, %γv, #Hvb⟩,
    ⟨%ltch, #Hltf, %γlt, #Hltb⟩, -, -, -, -, ⟨%cch, #Hcchf, %γq, #Hcchb⟩, ⟨%c3, #Hf3, %γ3, #Hb3⟩,
    ⟨%c1, #Hf1, %γ1, #Hb1⟩, ⟨%c5, #Hf5, %γ5, #Hb5⟩, ⟨%c8, #Hf8, %γ8, #Hb8⟩,
    ⟨%c10, #Hf10, %γ10, #Hb10⟩, ⟨%c11, #Hf11, %γ11, #Hb11⟩⟩
  ihave ⟨%x, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  unfold isTransport isRpcChan
  icases Htr with ⟨⟨%γrpc, #Hrpc⟩, -⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #HlocalID, -⟩
  ihave ⟨%eNL, #HeNL⟩ := isRaftErr_of_init (GF := GF) RaftErr.notLeader $$ Hpkg
  ihave #HgNL0 := isRaftErr_global RaftErr.notLeader eNL $$ HeNL
  ihave #HgNL : (globalAddr ErrNotLeader ↦□ eNL : IProp GF) $$ []
  · have e : RaftErr.notLeader.var = ErrNotLeader := rfl
    rw [← e]
    iexact HgNL0
  wp_auto
  wp_apply (wp_config r γ rc i) $$ [$Hr] with %c %Hc
  wp_apply (wp_randomTimeout) with %hb Hhb
  ihave HI : (∃ (ch : Loc) (b : Bool), "heartbeatTimer" ∷ heartbeatTimer_ptr ↦ ch ∗
      "Hhb" ∷ (⌜ch = chan.nil⌝ ∨ ∃ γc, isChanBag (V := time.Time) γc ch (fun _ => iprop(True))) ∗
      "didWarn" ∷ didWarn_ptr ↦ b ∗ "Hm" ∷ mainOwn r γ rc i ∗ "Htok" ∷ rtok tid : IProp GF)
    $$ [heartbeatTimer Hhb didWarn Hm Htok]
  · iexists hb, false; iframe
  wp_for HI
  icases (mainOwn_unfold r γ rc i).1 $$ Hm with ⟨%s, %st, Hm, Hl0⟩
  icases mainOwnAt_state' r γ rc i s st $$ Hm with ⟨Hst, Hm⟩
  wp_apply (wp_getState.1 r rc st) $$ [$Hsc $Hst] with Hst
  ihave Hm := Hm $$ Hst
  wp_if_destruct
  · have hst : st = stFollower := of_decide_eq_true (go.IntoValInj.intoVal_inj Hif)
    wp_apply_core chan.wp_select_blocking_nil
    -- rpcCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γrpc rpcCh (rpcP γ rc.snapP i) _ _ $$ Hrpc
      inext
      iintro %v Hv
      wp_auto
      wp_apply (wp_processRPC r γ rc i v s st) $$ [Hm Hv Htok] with ⟨%s', %st', Hm, Htok, Hkeep⟩
      · iframe; iframe #
      ihave %Hnl : ⌜st' ≠ stLeader⌝ $$ [Hkeep]
      · icases Hkeep with (%Hk | ⟨%Hk, -⟩)
        · ipureintro
          rcases Hk with h | ⟨h, -⟩ | ⟨h, -⟩ <;> subst h <;> (try rw [hst]) <;> decide
        · ipureintro; rw [Hk.1, hst]; decide
      wp_for_post
      iframe
      iexists ch, b
      iframe
      iapply mainOwnAt_mainOwn r γ rc i s' st' Hnl $$ Hm
    -- configurationChangeCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γ3 c3 (ccfP γ) _ _ $$ Hb3
      inext
      iintro %f Hf
      unfold ccfP
      icases Hf with ⟨%rq, %lv, %t, %v0, -, -, -, -, -, Hde⟩
      wp_auto
      wp_apply (deferError.respond_ccFuture wp_respond f cfgChangeQ eNL) $$ [Hde] with -
      · ileft; iframe
        unfold cfgChangeQ
        iright; ileft; iexists RaftErr.notLeader; iexact HeNL
      wp_for_post
      iframe
      iexists ch, b
      iframe
      iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide) $$ Hm
    -- applyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γa applyCh (applyP γ rc i) _ _ $$ Happly
      inext
      iintro %v Hv
      unfold applyP
      icases Hv with (⟨%d, %n, %lv, %tm, Hlog, %Hty, #Hdata, -, Hresp, Hdisp, Hde, Hop⟩ |
        ⟨%lv, %tm, %sc, Hlog, %Hty, #Hdata, -, Hresp, Hdisp, #Hsc, Hde⟩)
      · wp_auto
        wp_apply (deferError.respond_logFuture wp_respond v (futQ γ rc v d n) eNL) $$ [Hde Hop] with -
        · ileft; iframe
          unfold futQ
          ileft; iframe; ileft; iframe #
        wp_for_post
        iframe
        iexists ch, b
        iframe
        iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide) $$ Hm
      ihave %HnNL := isRaftErr_nonnil RaftErr.notLeader eNL $$ HeNL
      wp_auto
      wp_apply (deferError.respond_logFuture wp_respond v (barrierQ γ rc i sc) eNL) $$ [Hde] with -
      · ileft; iframe
        unfold barrierQ
        ileft; ipureintro; exact HnNL
      wp_for_post
      iframe
      iexists ch, b
      iframe
      iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide) $$ Hm
    -- verifyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γv vch (verifyP γ rc i vch) _ _ $$ Hvb
      inext
      iintro %v Hv
      ihave %HnNL := isRaftErr_nonnil RaftErr.notLeader eNL $$ HeNL
      icases mainOwnAt_registry r γ rc i s st $$ Hm with ⟨Hreg, Hm⟩
      wp_auto
      wp_apply (wp_verify_reject γ rc i vch v eNL HnNL) $$ [Hreg Hv] with Hreg
      · iframe
      wp_for_post
      iframe
      iexists ch, b
      iframe
      iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide)
      iapply Hm $$ Hreg
    -- userRestoreCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ5 c5 _ _ $$ Hb5
    -- leadershipTransferCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γlt ltch (ltfP γ i) _ _ $$ Hltb
      inext
      iintro %f Hf
      wp_auto
      wp_apply (wp_lt_reject γ i f eNL) $$ [Hf]
      · iframe
      wp_for_post
      iframe
      iexists ch, b
      iframe
      iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide) $$ Hm
    -- configurationsCh (stage 3: takeSnapshot's request)
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft
      iapply bag_clause' γq cch (cfgReqP γ rc i) _ _ $$ Hcchb
      inext
      iintro %f Hf
      unfold cfgReqP
      icases Hf with ⟨%x, %m, %hx, #Hbx, ⟨%cf0, Hcf⟩, Hde⟩
      ihave ⟨#HI, -⟩ := isRaft_proto r γ rc i $$ Hr
      imod mainOwnAt_cfgReq r γ rc i s st m x hx $$ [$HI $Hbx $Hm]
        with ⟨%ccfg, %cfg, %cidx, %li, %ss, Hcfgs, #Hcfg, #Hlat, #Hsnap, #Hdx, #Hax, #Hcx, Hm⟩
      ihave #Hcfg' := Hcfg
      unfold cfgVal
      icases Hcfg' with ⟨#Hss, %Hssok⟩
      unfold cfgOpt
      icases Hlat with ⟨%ls, #Hls, -⟩
      wp_auto
      wp_apply (configurations.wp_Clone wp_Clone _ ccfg cfg cidx li ss ls DFrac.discard
        DFrac.discard) $$ [$Hcfgs $Hss $Hls] as %cf ⟨Hcfgs, -, -, Hcs, %Hci⟩
      ihave Hm := Hm $$ Hcfgs
      imod ownSlice_persist $$ Hcs with #Hcs
      wp_apply (deferError.respond_cfgFuture wp_respond f (cfgReqQ γ rc i f x) interface.nil)
        $$ [Hde Hcf] with -
      · ileft; iframe
        unfold cfgReqQ
        ileft
        isplitr; · ipureintro; rfl
        iexists cf
        iframe
        iframe Hdx Hax Hcx
        iexists ss
        rw [Hci]
        iframe Hsnap
        unfold cfgVal
        iframe Hcs
        ipureintro; exact Hssok
      wp_for_post
      iframe
      iexists ch, b
      iframe
      iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide) $$ Hm
    -- bootstrapCh (so `liveBootstrap` is unreachable)
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ8 c8 _ _ $$ Hb8
    -- leaderNotifyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ10 c10 _ _ $$ Hb10
    -- followerNotifyCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ11 c11 _ _ $$ Hb11
    -- heartbeatTimer
    iapply BigAndL.bigAndL_cons.2; isplit
    · icases Hhb with (%Hnil | ⟨%γt, #Ht⟩)
      · iright; iapply chan.nilClausePre_recv time.Time _ _ Hnil
      ileft
      iapply bag_clause' γt ch _ _ _ $$ Ht
      inext
      iintro %v -
      wp_auto
      wp_apply (wp_config r γ rc i) $$ [$Hr] with %c' %Hc'
      wp_apply wp_randomTimeout with %hb' Hhb'
      wp_apply (wp_LastContact r γ rc i) $$ [$Hr $Htok] with %lc Htok
      wp_apply wp_Since with %d -
      wp_if_destruct
      · wp_for_post
        iframe; iexists hb', b; iframe
        iapply mainOwnAt_mainOwn r γ rc i s st (by rw [hst]; decide) $$ Hm
      wp_apply (wp_setLeader r γ rc i) $$ [$Hr $Htok] with Htok
      icases mainOwnAt_split r γ rc i s st $$ Hm with ⟨%cfg, %ccfg, %cidx, %li, Hcfgs, #Hcfg, %Hli, Hst, Hm⟩
      icases cfgAtIs_srvs γ s.log _ cfg $$ Hcfg with ⟨%ss, #Hss, %Hsok⟩
      wp_auto
      repeat' (first
        | wp_if_destruct
        | (wp_apply (wp_hasVote cfg ss DFrac.discard i) $$ [$Hss] as -)
        | wp_auto
        | (cases b <;> wp_auto))
      all_goals (first
        | (ipureintro; exact Hsok.2.2)
        | (wp_apply (wp_setState r γ rc i st (W32 1) s) $$ [Hst Htok] with ⟨Hst, -, Htok⟩
           · iframe; iframe #
             isplitr
             · ipureintro; right; left; rfl
             iapply obsArg_candidate' γ i s
           wp_for_post
           iapply HΦ
           iframe
           iapply mainOwnAt_mainOwn (st := W32 1) (h := by decide)
           iapply Hm $$ [] Hcfgs Hst
           ipureintro; left; decide)
        | (wp_for_post; iframe; iexists hb', _; iframe;
           iapply mainOwnAt_mainOwn (st := st) (h := by rw [hst]; decide); iapply Hm $$ [] Hcfgs Hst;
           ipureintro; exact Or.inr rfl))
    -- shutdownCh
    iapply BigAndL.bigAndL_cons.2; isplit
    · ileft; iapply dead_clause' γ1 c1 _ _ $$ Hb1
    iapply BigAndL.bigAndL_nil.2
    itrivial
  split
  · rename_i h; exfalso; simp only [decide_eq_true_eq] at h; subst h; exact Hif (by simp)
  wp_auto
  iapply HΦ; iframe; iapply mainOwn_intro; iframe

end proof

end Perennial
