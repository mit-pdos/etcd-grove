/-
The hraft kit's receiver over the service spec `raftSvc` (`rpctransport/Facts.lean`): the
`RaftRPC` methods' specs (S4b's, `Spec/.../rpctransport/RaftRPC__*.lean`, taken as hypotheses, a
proof's callees) give the receiver's obligations `RaftRcvLaws` (`CodecRcv.lean`) for
`raftSvc γ snapP i`, with `rcvP` (the package and `isRcv`) as the receiver's persistent facts: a
deposit's request is the decoded one (`encAEReq_inj`, ...: the deposit is of an encoding of it, which
is a slice's bytes), and the method's response facts are the deposit's success answer. With
`raftRcv`, a server's `*RaftRPC` is a net/rpc receiver of `raftSvc` (`Server.Register`'s premise):
`raftRcv_raftSvc`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecRcv
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__AppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__InstallSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__RequestPreVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__RequestVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__TimeoutNow

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [rpcpkg : rpctransport.Assumptions]

/-- The receiver's persistent facts: the package and `isRcv`. -/
abbrev rcvP (s : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID)
    (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
    isRcv s γ snapP i W C)

theorem rcvMeth_AppendEntries (wp : RaftRPC.AppendEntries.spec (GF := GF)) (s : Loc) (γ : GNames)
    (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    rpcMeth.spec (rcvP s γ snapP i W C) s go!"AppendEntries" aeReqOwn encAEReq aeRespOwn encAEResp
      (raftSvc γ snapP i go!"AppendEntries") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hrcv⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold raftSvc
  rw [ if_pos rfl]
  icases HS with ⟨%v, %snd, %T, %prev, %pt, %ents, %lci, %ss, %Hbs, Hreq, Hans⟩
  obtain rfl := encAEReq_inj va v (by omega) Hbs
  wp_apply (wp s γ snapP i W C ap rp wa _ snd T prev pt ents lci ss) $$ [Hp Hown Hr Hreq] as ⟨%w', %r, Hr, Hrown, Hresp⟩
  · iframe Hp Hown Hr Hreq
    iframe
    iexact Hrcv
  iapply HΨ
  iexists w', r
  iframe Hr Hrown
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists r
  iframe
  ipureintro; rfl

theorem rcvMeth_RequestVote (wp : RaftRPC.RequestVote.spec (GF := GF)) (s : Loc) (γ : GNames)
    (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    rpcMeth.spec (rcvP s γ snapP i W C) s go!"RequestVote" voteReqOwn encVoteReq voteRespOwn encVoteResp
      (raftSvc γ snapP i go!"RequestVote") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hrcv⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold raftSvc
  rw [if_neg (by decide), if_pos rfl]
  icases HS with ⟨%v, %c, %T, %li, %lt, %Hbs, Hreq, Hans⟩
  obtain rfl := encVoteReq_inj va v (by omega) Hbs
  wp_apply (wp s γ snapP i W C ap rp wa _ c T li lt) $$ [Hp Hown Hr Hreq] as ⟨%w', %r, Hr, Hrown, Hresp⟩
  · iframe Hp Hown Hr Hreq
    iframe
    iexact Hrcv
  iapply HΨ
  iexists w', r
  iframe Hr Hrown
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists r
  iframe
  ipureintro; rfl

theorem rcvMeth_RequestPreVote (wp : RaftRPC.RequestPreVote.spec (GF := GF)) (s : Loc) (γ : GNames)
    (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    rpcMeth.spec (rcvP s γ snapP i W C) s go!"RequestPreVote" preVoteReqOwn encPreVoteReq preVoteRespOwn encPreVoteResp
      (raftSvc γ snapP i go!"RequestPreVote") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hrcv⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold raftSvc
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  icases HS with ⟨%v, %c, %T, ⟨%Hbs, %Hpv⟩, Hans⟩
  obtain rfl := encPreVoteReq_inj va v (by omega) Hbs
  wp_apply (wp s γ snapP i W C ap rp wa _ c T) $$ [Hp Hown Hr] as ⟨%w', %r, Hr, Hrown, Hresp⟩
  · iframe Hp Hown Hr
    iframe
    isplitr
    · iexact Hrcv
    · ipureintro; exact Hpv
  iapply HΨ
  iexists w', r
  iframe Hr Hrown
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists r
  iframe
  ipureintro; rfl

theorem rcvMeth_InstallSnapshot (wp : RaftRPC.InstallSnapshot.spec (GF := GF)) (s : Loc) (γ : GNames)
    (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    rpcMeth.spec (rcvP s γ snapP i W C) s go!"InstallSnapshot" snapReqOwn encSnapReq snapRespOwn encSnapResp
      (raftSvc γ snapP i go!"InstallSnapshot") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hrcv⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold raftSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  icases HS with ⟨%v, %snd, %T, %s0, %st, %Hbs, Hreq, Hans⟩
  obtain rfl := encSnapReq_inj va v (by omega) Hbs
  wp_apply (wp s γ snapP i W C ap rp wa _ snd T s0 st) $$ [Hp Hown Hr Hreq] as ⟨%w', %r, Hr, Hrown, Hresp⟩
  · iframe Hp Hown Hr Hreq
    iframe
    iexact Hrcv
  iapply HΨ
  iexists w', r
  iframe Hr Hrown
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists r
  iframe
  ipureintro; rfl

theorem rcvMeth_TimeoutNow (wp : RaftRPC.TimeoutNow.spec (GF := GF)) (s : Loc) (γ : GNames)
    (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    rpcMeth.spec (rcvP s γ snapP i W C) s go!"TimeoutNow" (fun (w : rpctransport.TimeoutReq) dq h => hdrOwn (GF := GF) w.Hdr' dq h) encTimeoutReq timeoutRespOwn encTimeoutResp
      (raftSvc γ snapP i go!"TimeoutNow") := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨#Hpk, #Hrcv⟩, %Hl, HS, Hp, Hown, Hr⟩ HΨ
  unfold raftSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  icases HS with ⟨%h, %c, ⟨%Hbs, %Htn⟩, Hans⟩
  obtain rfl := encTimeoutReq_inj va h (by omega) Hbs
  wp_apply (wp s γ snapP i W C ap rp wa _ c) $$ [Hp Hown Hr] as ⟨%w', %r, Hr, Hrown⟩
  · iframe Hp Hown Hr
    iframe
    isplitr
    · iexact Hrcv
    · ipureintro; exact Htn
  iapply HΨ
  iexists w', r
  iframe Hr Hrown
  unfold answers
  icases Hans with ⟨Hok, -⟩
  iapply Hok
  iexists r
  iframe
  ipureintro; rfl

/-- **A server's `*RaftRPC` `s` meets the receiver's obligations for `raftSvc γ snapP i`**, from the
methods' specs. -/
theorem raftRcvLaws_of (wpAE : RaftRPC.AppendEntries.spec (GF := GF))
    (wpIS : RaftRPC.InstallSnapshot.spec (GF := GF)) (wpPV : RaftRPC.RequestPreVote.spec (GF := GF))
    (wpRV : RaftRPC.RequestVote.spec (GF := GF)) (wpTN : RaftRPC.TimeoutNow.spec (GF := GF))
    (s : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF)
    (C : net.rpc.CodecSpec GF) :
    RaftRcvLaws (rcvP s γ snapP i W C) s (raftSvc γ snapP i) where
  enc_AppendEntries := raftSvc_encOf_AppendEntries γ snapP i
  meth_AppendEntries := rcvMeth_AppendEntries wpAE s γ snapP i W C
  enc_InstallSnapshot := raftSvc_encOf_InstallSnapshot γ snapP i
  meth_InstallSnapshot := rcvMeth_InstallSnapshot wpIS s γ snapP i W C
  enc_RequestPreVote := raftSvc_encOf_RequestPreVote γ snapP i
  meth_RequestPreVote := rcvMeth_RequestPreVote wpPV s γ snapP i W C
  enc_RequestVote := raftSvc_encOf_RequestVote γ snapP i
  meth_RequestVote := rcvMeth_RequestVote wpRV s γ snapP i W C
  enc_TimeoutNow := raftSvc_encOf_TimeoutNow γ snapP i
  meth_TimeoutNow := rcvMeth_TimeoutNow wpTN s γ snapP i W C

/-- **A server's `*RaftRPC` `s` is a net/rpc receiver of `raftSvc γ snapP i`** (`Server.Register`'s
premise `C.rcv rcvr (rcvrIs ...)`), from the methods' specs. -/
theorem raftRcv_raftSvc (wpAE : RaftRPC.AppendEntries.spec (GF := GF))
    (wpIS : RaftRPC.InstallSnapshot.spec (GF := GF)) (wpPV : RaftRPC.RequestPreVote.spec (GF := GF))
    (wpRV : RaftRPC.RequestVote.spec (GF := GF)) (wpTN : RaftRPC.TimeoutNow.spec (GF := GF))
    (s : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF)
    (C : net.rpc.CodecSpec GF) :
    ⌜s ≠ null⌝ ∗ net.rpc.codecSet (hraftCodec (GF := GF)) ∗ rcvP s γ snapP i W C ⊢
    (hraftCodec (GF := GF)).rcv (ptrI RaftRPC.ty s)
      (net.rpc.rcvrIs hraftCodec (ptrI RaftRPC.ty s) (raftSvc γ snapP i) go!"RaftRPC" false) :=
  raftRcv _ s _ (raftRcvLaws_of wpAE wpIS wpPV wpRV wpTN s γ snapP i W C)

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
