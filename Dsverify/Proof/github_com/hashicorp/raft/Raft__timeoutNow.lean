/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__timeoutNow.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).timeoutNow` (stage 2): `setLeader("", "")`, `setState(Candidate)`, the
transfer flag set, and the (empty) response.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__timeoutNow
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setState
public import Dsverify.Spec.github_com.hashicorp.raft.RPC__Respond
public import Dsverify.Proof.github_com.hashicorp.raft.main.MainCLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base
public import Perennial.Spec.sync.atomic.Bool__Store

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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.timeoutNow.wp_proof
    (wp_setLeader : github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG))
    (wp_setState : github_com.hashicorp.raft.Raft.setState.spec (GF := GF) (hG := hG))
    (wp_Respond : github_com.hashicorp.raft.RPC.Respond.spec (GF := GF) (hG := hG))
    (wp_Bool_Store : sync.atomic.Bool.Store.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.timeoutNow.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc p rq γc s st tid => by
  wp_start as ⟨#Hr, Hm, Htok, Hp, #Hbag⟩
  ihave #Hcft := isRaft_cftCell r γ rc i $$ Hr
  wp_auto
  wp_apply wp_setLeader r γ rc i _ _ $$ [$Hr $Htok] as Htok
  icases mainOwnAt_split r γ rc i s st $$ Hm with ⟨%cfg, %ccfg, %cidx, %li, Hc, #Hcfg, %Hli, Hst, Hm⟩
  rw [show (Candidate : val) = #stCandidate from rfl]
  wp_apply wp_setState r γ rc i _ stCandidate s $$ [$Hr $Hst $Htok] as ⟨Hst, -, Htok⟩
  · isplitr; · ipureintro; right; left; rfl
    iapply obsArg_state γ i s stCandidate (by decide)
  wp_apply wp_cft_Store wp_Bool_Store r true $$ [$Hcft]
  wp_alloc q as Hq
  wp_auto
  wp_apply wp_Respond rpc_ptr rpc γc _ _ _ $$ [$rpc $Hbag Hq] as rpc
  · unfold rpcRespOkP
    iexists q
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists _
    iframe Hq
    iexists [], []
    isplitl
    · iapply ownSlice_nil
    · iapply ownSlice_nil
  iapply HΦ
  iframe Htok
  iapply Hm $$ %stCandidate [] [$Hc] [$Hst]
  ipureintro; left; decide

end proof

end Perennial
