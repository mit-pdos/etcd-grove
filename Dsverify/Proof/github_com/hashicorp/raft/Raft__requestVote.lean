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
    github_com.hashicorp.raft.Raft.requestVote.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
