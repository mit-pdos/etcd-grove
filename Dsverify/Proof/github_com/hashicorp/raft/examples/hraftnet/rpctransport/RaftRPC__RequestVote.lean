/-
The proof of `rpctransport.RaftRPC.RequestVote`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__RequestVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromVoteReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__deliver

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport


theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.RequestVote.wp_proof
    (wp_fromVoteReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromVoteReq.spec (GF := GF) (hG := hG))
    (wp_toVoteResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteResp.spec (GF := GF) (hG := hG))
    (wp_deliver : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.RequestVote.spec (GF := GF) (hG := hG) := by
  intro s γ snapP i W C args reply w v c T li lt
  wp_start as ⟨#Hs, Hargs, Hown, Hreq, Hrep⟩
  unfold isRcv
  icases Hs with ⟨%t, #Hs, #Ht⟩
  unfold voteReqOwn hdrOwn
  icases Hown with ⟨%Hw, ⟨%Hpv, Hid, Had⟩, Hcand⟩
  unfold rvReqW
  icases Hreq with ⟨%Hv, Hci⟩
  wp_auto
  wp_apply wp_fromVoteReq $$ [$Hargs $Hid $Had $Hcand] as %p ⟨Hargs, Hid, Had, Hcand, %i0, %d0, %c0, Hp, Hi, Hd, Hc⟩
  obtain ⟨hT, hli, hlt, ⟨hpv3, hid, had⟩, hcand⟩ := Hv
  obtain ⟨hwT, hwli, hwlt, -⟩ := Hw
  ipersist Hi
  ipersist Hd
  ipersist Hc
  ihave #Hi' : (i0 ↦*□ c : IProp GF) $$ [Hi]
  · rw [← hid]; iexact Hi
  ihave #Hd' : (d0 ↦*□ c : IProp GF) $$ [Hd]
  · rw [← had]; iexact Hd
  ihave #Hc' : (c0 ↦*□ c : IProp GF) $$ [Hc]
  · rw [← hcand]; iexact Hc
  ihave Hs2 : (s ↦□ RaftRPC.mk t : IProp GF) $$ []
  · iexact Hs
  iStructNamed Hs2
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  wp_auto
  wp_apply (wp_deliver t γ snapP i W C _ _ false
      (github_com.hashicorp.raft.rpcRespP github_com.hashicorp.raft.RequestVoteResponse.ty
        (fun q => iprop(∃ rp : github_com.hashicorp.raft.RequestVoteResponse, q ↦ rp ∗
          github_com.hashicorp.raft.rvResp γ rp i c T)))) $$ [$Ht Hp Hci]
    as %res %err ⟨%r, ⟨%Hres, %Herr⟩, HQ⟩
  · iintro %ch %γc #Hb
    isplit
    · unfold github_com.hashicorp.raft.rpcP
      ileft
      isplitr
      · ipureintro; rfl
      iright; ileft
      iexists p, _, c, T, li, lt, γc
      iframe Hp Hb
      isplitr
      · ipureintro; rfl
      unfold github_com.hashicorp.raft.rvReq github_com.hashicorp.raft.hdrOk
      iframe Hi' Hd' Hc' Hci
      ipureintro
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hwT]; exact hT
      · rw [hwli]; exact hli
      · rw [hwlt]; exact hlt
      · rw [Hpv]; exact hpv3
    · iintro %Hf
      exact absurd Hf (by decide)
  subst Herr Hres
  unfold github_com.hashicorp.raft.rpcRespP
  icases HQ with (#Heok | ⟨%q, ⟨%Hen, %Hrq⟩, %rp, Hq, Hrv⟩)
  · iunfold github_com.hashicorp.raft.errOk at Heok
    icases Heok with ⟨%x, %Hx, #HE⟩
    rw [Hx]
    wp_auto
    wp_bind (App (Val #(methods x.ty _ x.v)) (Val #()))
    iapply HE
    iintro %msg
    wp_auto
    iapply HΦ
    iexists _, ⟨true, msg, ⟨(zeroValDef : VoteResp).Hdr'.ProtocolVersion', [], []⟩,
      (zeroValDef : VoteResp).Term', [], (zeroValDef : VoteResp).Granted'⟩
    iframe Hrep
    unfold voteRespOwn hdrOwn rvRespW
    isplitr
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitr
      · isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownSlice_nil
        · iapply ownSlice_nil
      · iapply ownSlice_nil
    · ileft; ipureintro; rfl
  · rw [Hen, Hrq]
    wp_auto
    iunfold github_com.hashicorp.raft.rvResp at Hrv
    icases Hrv with ⟨Hterm, Hg, ⟨%pb, #Hpb⟩, ⟨%snd, Hh⟩⟩
    iunfold github_com.hashicorp.raft.hdrOk at Hh
    icases Hh with ⟨%Hpv3, #Hid0, #Had0⟩
    wp_apply wp_toVoteResp $$ [$Hq $Hid0 $Had0 $Hpb] as %i1 %d1 %c1 ⟨Hq, -, -, -, Hi1, Hd1, Hc1⟩
    (try wp_auto)
    iapply HΦ
    iexists _, ⟨false, [], ⟨rp.RPCHeader'.ProtocolVersion', snd, snd⟩, rp.Term', pb, rp.Granted'⟩
    iframe Hrep
    unfold voteRespOwn hdrOwn rvRespW
    isplitl [Hi1 Hd1 Hc1]
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      iframe Hc1
      isplitr
      · ipureintro; rfl
      iframe Hi1 Hd1
    · iright
      isplitr
      · ipureintro; rfl
      iframe Hterm Hg
      ipureintro
      exact ⟨snd, Hpv3, rfl, rfl⟩

end proof

end Perennial
