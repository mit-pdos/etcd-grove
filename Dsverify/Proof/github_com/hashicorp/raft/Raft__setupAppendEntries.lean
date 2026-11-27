/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setupAppendEntries.lean (241f27e).
-/
/-
The proof of `Raft__setupAppendEntries` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setupAppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setPreviousLog
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setNewLogs

@[expose] public section

set_option linter.unusedVariables false

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

theorem github_com.hashicorp.raft.Raft.setupAppendEntries.wp_proof
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_setPreviousLog : github_com.hashicorp.raft.Raft.setPreviousLog.spec (GF := GF) (hG := hG))
    (wp_setNewLogs : github_com.hashicorp.raft.Raft.setNewLogs.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setupAppendEntries.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s req rq nextIndex lastIndex tid => by
  wp_start as ⟨#Hr, #Hs, #Hl, #Hlb, Hreq, Htok⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_getRPCHeader $$ [$Hr] as %h #Hh
  unfold replShared
  icases Hs with ⟨%cm, %stopCh, %trig, %notif, %sd, %tde, %γs, #HcurT, -⟩
  ihave ⟨%x, %rpcCh, #Htrans, #HrpcCh, #Ht⟩ := isRaft_transport r γ rc i $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #Hid, #Haddr, -⟩
  wp_auto
  unfold isTransport
  icases Ht with ⟨-, -, -, #HEnc, -⟩
  wp_bind (App (App (Val #(methods x.ty _ x.v)) _) _)
  iapply HEnc
  iintro %lsl Hlsl
  ipersist Hlsl
  ihave ⟨#Hinv, -⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hcc := isRaft_cidxCell r γ rc i $$ Hr
  wp_auto
  wp_apply wp_getCommitIndex.2 $$ [$Hinv $Hcc $Hl $Hlb] as %ci #Hci
  wp_apply wp_setPreviousLog $$ [$Hr $Hl $Hlb $Hreq $Htok] as %err ⟨Htok, %prev, %pt, Hreq, Hres⟩
  icases Hres with (⟨%Herr, #Hce⟩ | ⟨⟨%Herr, %Hprev⟩, #Hpo⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    imodintro
    iapply HΦ
    iframe Htok
    iexists _
    iframe Hreq
    ileft; iframe #; ipureintro; exact Herr
  subst Herr
  wp_auto
  wp_apply wp_setNewLogs $$ [$Hr $Hl $Hlb $Hreq $Htok] as %err ⟨Htok, %sl, Hreq, Hres⟩
  · ipureintro; exact Hprev
  icases Hres with (⟨%Herr, #Hce⟩ | ⟨%Herr, %ents, #Hptrs, #Heo⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    imodintro
    iapply HΦ
    iframe Htok
    iexists _
    iframe Hreq
    ileft; iframe #; ipureintro; exact Herr
  subst Herr
  wp_auto
  imodintro
  iapply HΦ
  iframe Htok
  iexists _
  iframe Hreq
  iright
  isplitr; · ipureintro; rfl
  iexists (uint.nat prev), (uint.nat pt), ents, (uint.nat ci)
  isplitr
  · unfold aeBody
    iframe #
    ipureintro
    exact ⟨rfl, rfl, rfl, rfl⟩
  iapply aeValid_of_reads γ i T (uint.nat prev) (uint.nat pt) ents (uint.nat ci)
  iframe #

end proof

end Perennial
