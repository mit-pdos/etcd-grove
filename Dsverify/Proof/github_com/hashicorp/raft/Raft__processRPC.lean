/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__processRPC.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).processRPC`: the header check passes, and the type switch dispatches to
the handler of the request's kind (the default branch is unreachable: `rpcP` gives only the five
kinds the program sends; stage 2: `TimeoutNow` makes a candidate; stage 3: `InstallSnapshot`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processRPC
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__checkRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__appendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__requestVote
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__requestPreVote
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__timeoutNow
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__installSnapshot
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base

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

theorem isReq_ver (γ : GNames) (rq : InstallSnapshotRequest) snd j T s st b :
    isReq (GF := GF) γ rq snd j T s st b ⊢
      isReq γ rq snd j T s st b ∗ ⌜rq.RPCHeader'.ProtocolVersion' = W64 3⌝ := by
  unfold isReq
  iintro ⟨%Hn, #Hh, #H1, #H2, #H3, #H4, #H5⟩
  ihave %Hv : ⌜rq.RPCHeader'.ProtocolVersion' = W64 3⌝ $$ [Hh]
  · unfold hdrOk; icases Hh with ⟨%h, -⟩; ipureintro; exact h
  iframe; iframe #; ipureintro; exact ⟨Hn, Hv⟩

theorem github_com.hashicorp.raft.Raft.processRPC.wp_proof
    (wp_checkRPCHeader : github_com.hashicorp.raft.Raft.checkRPCHeader.spec (GF := GF) (hG := hG))
    (wp_appendEntries : github_com.hashicorp.raft.Raft.appendEntries.spec (GF := GF) (hG := hG))
    (wp_requestVote : github_com.hashicorp.raft.Raft.requestVote.spec (GF := GF) (hG := hG))
    (wp_requestPreVote : github_com.hashicorp.raft.Raft.requestPreVote.spec (GF := GF) (hG := hG))
    (wp_timeoutNow : github_com.hashicorp.raft.Raft.timeoutNow.spec (GF := GF) (hG := hG))
    (wp_installSnapshot : github_com.hashicorp.raft.Raft.installSnapshot.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.processRPC.spec (GF := GF) (hG := hG) :=
  fun r γ rc i rpc s st tid => by
  wp_start as ⟨#Hr, Hm, Hrpc, Htok⟩
  unfold rpcP aeRpcP
  icases Hrpc with (⟨%Hrd, (⟨%p, %rq, %snd, %T, %prev, %pt, %ents, %lci, %ss, %γc, %Hc, Hp, Hreq, #Hbag⟩ |
    ⟨%p, %rq, %c, %T, %li, %lt, %γc, %Hc, Hp, Hreq, #Hbag⟩ | ⟨%p, %rq, %c, %T, %γc, %Hc, Hp, Hreq, #Hbag⟩ |
    ⟨%p, %rq, %c, %γc, %Hc, Hp, Hreq, #Hbag⟩)⟩ | Hisr)
  · ihave %Hv := aeReq_ver $$ Hreq
    wp_auto
    wp_apply wp_checkRPCHeader.1 r γ rc i rpc p rq $$ [$Hr $Hp] as Hp
    · ipureintro; exact ⟨Hc, Hv⟩
    rw [Hc]
    wp_auto
    wp_apply wp_appendEntries $$ [$Hr $Hm $Htok $Hp $Hreq $Hbag] as ⟨%s', %st', Hm, Htok, Hst'⟩
    wp_end
    iexists s', st'
    iframe
    icases Hst' with (%Hst' | Hst')
    · ileft; ipureintro; rcases Hst' with h | h
      · left; exact h
      · right; left; exact h
    · iright; iexact Hst'
  · ihave %Hv := rvReq_ver $$ Hreq
    wp_auto
    wp_apply wp_checkRPCHeader.2.1 r γ rc i rpc p rq $$ [$Hr $Hp] as Hp
    · ipureintro; exact ⟨Hc, Hv⟩
    rw [Hc]
    wp_auto
    wp_apply wp_requestVote $$ [$Hr $Hm $Htok $Hp $Hreq $Hbag] as ⟨%s', %st', Hm, Htok, %Hst'⟩
    wp_end
    iexists s', st'
    iframe
    ileft; ipureintro; rcases Hst' with h | h
    · left; exact h
    · right; left; exact h
  · ihave %Hv := pvReq_ver $$ Hreq
    wp_auto
    wp_apply wp_checkRPCHeader.2.2.1 r γ rc i rpc p rq $$ [$Hr $Hp] as Hp
    · ipureintro; exact ⟨Hc, Hv⟩
    rw [Hc]
    wp_auto
    wp_apply wp_requestPreVote $$ [$Hr $Hm $Htok $Hp $Hreq $Hbag] as ⟨%s', %st', Hm, Htok, %Hst'⟩
    wp_end
    iexists s', st'
    iframe
    ileft; ipureintro; rcases Hst' with h | h
    · left; exact h
    · right; left; exact h
  · unfold tnReq
    unfold hdrOk
    icases Hreq with ⟨%Hv, -⟩
    wp_auto
    wp_apply wp_checkRPCHeader.2.2.2.1 r γ rc i rpc p rq $$ [$Hr $Hp] as Hp
    · ipureintro; exact ⟨Hc, Hv⟩
    rw [Hc]
    wp_auto
    wp_apply wp_timeoutNow $$ [$Hr $Hm $Htok $Hp $Hbag] as ⟨Hm, Htok⟩
    wp_end
    iexists s, stCandidate
    iframe
    ileft; ipureintro; right; right; exact ⟨rfl, rfl, rfl⟩
  · -- (stage 3) InstallSnapshot
    unfold isRpcP
    icases Hisr with ⟨%p, %rq, %snd, %T, %s0, %st0, %b, %rd, %γc, %Hc, Hp, Hreq, Hstr, #Hbag⟩
    ihave ⟨Hreq, %Hv⟩ := isReq_ver $$ Hreq
    wp_auto
    wp_apply wp_checkRPCHeader.2.2.2.2 r γ rc i rpc p rq $$ [$Hr $Hp] as Hp
    · ipureintro; exact ⟨Hc.1, Hv⟩
    rw [Hc.1]
    wp_auto
    wp_apply wp_installSnapshot r γ rc i rpc p s st tid $$ [$Hr $Hm $Htok Hp Hreq Hstr] as
      ⟨%s', %st', Hm, Htok, Hst'⟩
    · isplitl
      · unfold isRpcP
        iexists p, rq, snd, T, s0, st0, b, rd, γc
        iframe
        iframe Hbag
        ipureintro; exact Hc
      ipureintro; exact Hc.1
    wp_end
    iexists s', st'
    iframe
    icases Hst' with (%Hst' | Hst')
    · ileft; ipureintro; rcases Hst' with h | h
      · left; exact h
      · right; left; exact h
    · iright; iexact Hst'
