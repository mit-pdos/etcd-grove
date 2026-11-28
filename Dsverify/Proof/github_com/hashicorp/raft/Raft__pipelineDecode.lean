/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__pipelineDecode.lean (241f27e).
-/
/-
The proof of `Raft__pipelineDecode` (replication subsystem, stage 2).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__pipelineDecode
public import Dsverify.Spec.github_com.hashicorp.raft.appendStats
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__handleStaleTerm
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.updateLastAppended
public import Dsverify.Proof.github_com.hashicorp.raft.ReplNotify
public import Dsverify.Proof.github_com.hashicorp.raft.ReplPipe

@[expose] public section

set_option linter.unusedVariables false
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

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.Raft.pipelineDecode.wp_proof
    (wp_updateLastAppended : github_com.hashicorp.raft.updateLastAppended.spec (GF := GF) (hG := hG))
    (wp_appendStats : github_com.hashicorp.raft.appendStats.spec (GF := GF) (hG := hG))
    (wp_handleStaleTerm : github_com.hashicorp.raft.Raft.handleStaleTerm.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.pipelineDecode.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s pI stopCh finCh γst γf tid => by
  wp_start as ⟨#Hr, #Hs, #Hp, #Hstop, Hcons, #Hfin, Hcl, Hnext, Htok⟩
  ihave ⟨#HcurT, ⟨%psf, #Hpeer⟩, #Hvj, #Hpl, -⟩ := replShared_core r γ i T j s $$ Hs
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, -, -, -, ⟨%nlt, #Hnlt⟩, -⟩
  wp_apply wp_with_defer as %defer Hdefer
  unfold isPipeline
  icases Hp with ⟨-, #HCons, -⟩
  wp_bind (App (Val #(methods pI.ty _ pI.v)) _)
  iapply HCons
  iintro %rch ⟨%γr, #Hrb⟩
  wp_auto_lc 4
  ihave HL : iprop(£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1) $$ [Hlc1 Hlc2 Hlc3 Hlc4]
  · iframe
  wp_for
  icases HL with ⟨Hc1, Hc2, Hc3, Hc4⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a response
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, rch, γr
    isplitr; · ipureintro; rfl
    isplitr; · iapply is_bag_is_chan $$ Hrb
    iapply bag_recv_au $$ [$Hc1 $Hc2] Hrb
    inext
    iintro %fi Hfut
    wp_auto_lc 5
    unfold rwLock
    icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
    imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
    wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
    wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP] as Hown
    imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
    unfold pipeFut
    icases Hfut with ⟨%fI, %args, %resp, %rq, %snd, %prev, %pt, %ents, %lci, %ss, %rp, %Hfi, #Hargs,
      #Haer, Hresp, Hpr, #HReq, #HResp, #HStart⟩
    subst Hfi
    wp_auto
    wp_bind (App (Val #(methods fI.ty _ fI.v)) _)
    iapply HReq
    wp_auto
    wp_bind (App (Val #(methods fI.ty _ fI.v)) _)
    iapply HResp
    wp_auto
    wp_bind (App (Val #(methods fI.ty _ fI.v)) _)
    iapply HStart
    iintro %st
    ihave ⟨#HE, -⟩ := (AccessStrict.access_strict
      (self := github_com.hashicorp.raft.AppendEntriesRequest.AppendEntriesRequest_access_load_Entries args rq DFrac.discard)) $$ Hargs
    ihave ⟨#HT, -⟩ := (AccessStrict.access_strict
      (self := github_com.hashicorp.raft.AppendEntriesRequest.AppendEntriesRequest_access_load_Term args rq DFrac.discard)) $$ Hargs
    wp_auto
    wp_apply wp_appendStats
    rcases rp with ⟨hdr1, tm1, ll1, succ1, nrb1⟩
    dsimp only
    wp_if_destruct
    · -- a newer term: stop
      wp_apply wp_handleStaleTerm $$ [$Hr $Hs]
      wp_for_post
      wp_apply (wp_fin_close γf finCh (nextHalf s)) $$ [$Hfin $Hcl $Hnext]
      iapply HΦ $$ Htok
    wp_apply wp_setLastContact $$ [$Hs]
    cases succ1
    · -- a failure: stop
      wp_auto
      wp_for_post
      wp_apply (wp_fin_close γf finCh (nextHalf s)) $$ [$Hfin $Hcl $Hnext]
      iapply HΦ $$ Htok
    -- a success: `j` acknowledged the request's entries in `T`
    wp_auto
    unfold pipeResp
    icases Hpr with (%Hf | %Hhb | #Hack)
    · exfalso; simp at Hf
    · wp_apply (wp_updateLastAppended r γ rc i T j s args rq snd prev pt ents lci
        DFrac.discard) $$ [$Hs $Hnext $Hargs] as ⟨Hnext, -⟩
      · iframe
        isplitr; · iapply aeBody_of_aeReq $$ Haer
        ileft; ipureintro; exact Hhb.2.1
      wp_for_post
      iframe
      isplitl [Hlc2]; · iexact Hlc2
      isplitl [Hlc3]; · iexact Hlc3
      isplitl [Hlc4]; · iexact Hlc4
      iexact Hlc5
    · wp_apply (wp_updateLastAppended r γ rc i T j s args rq snd prev pt ents lci
        DFrac.discard) $$ [$Hs $Hnext $Hargs] as ⟨Hnext, -⟩
      · iframe
        isplitr; · iapply aeBody_of_aeReq $$ Haer
        iright; iexact Hack
      wp_for_post
      iframe
      isplitl [Hlc2]; · iexact Hlc2
      isplitl [Hlc3]; · iexact Hlc3
      isplitl [Hlc4]; · iexact Hlc4
      iexact Hlc5
  iapply BigAndL.bigAndL_singleton.2
  -- the stop channel's close
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stopCh, γst.chanName
  isplitr; · ipureintro; rfl
  unfold hbStop
  isplitr
  · unfold isSpsc; icases Hstop with ⟨#Hc, -⟩; iexact Hc
  iapply spsc_rcv_au $$ Hstop [$Hc3 $Hc4] Hcons
  inext
  iintro %u %ok Hok
  cases ok
  · wp_auto
    wp_for_post
    wp_apply (wp_fin_close γf finCh (nextHalf s)) $$ [$Hfin $Hcl $Hnext]
    iapply HΦ $$ Htok
  · simp only [↓reduceIte]
    icases Hok with ⟨Hf, -⟩
    iexfalso; iexact Hf

end proof

end Perennial
