/-
The proof of `rpctransport.RaftRPC.RequestPreVote`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__RequestPreVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toPreVoteResp
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


theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.RequestPreVote.wp_proof
    (wp_fromPreVoteReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteReq.spec (GF := GF) (hG := hG))
    (wp_toPreVoteResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toPreVoteResp.spec (GF := GF) (hG := hG))
    (wp_deliver : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.RequestPreVote.spec (GF := GF) (hG := hG) := by
  intro s γ snapP i W C args reply w v c T
  wp_start as ⟨#Hs, Hargs, Hown, %Hv, Hrep⟩
  unfold isRcv
  icases Hs with ⟨%t, #Hs, #Ht⟩
  unfold preVoteReqOwn hdrOwn
  icases Hown with ⟨%Hw, ⟨%Hpv, Hid, Had⟩⟩
  wp_auto
  wp_apply wp_fromPreVoteReq $$ [$Hargs $Hid $Had] as %p ⟨Hargs, Hid, Had, %i0, %d0, Hp, Hi, Hd⟩
  obtain ⟨hT, ⟨hpv3, hid, had⟩⟩ := Hv
  obtain ⟨hwT, -⟩ := Hw
  ipersist Hi
  ipersist Hd
  ihave #Hi' : (i0 ↦*□ c : IProp GF) $$ [Hi]
  · rw [← hid]; iexact Hi
  ihave #Hd' : (d0 ↦*□ c : IProp GF) $$ [Hd]
  · rw [← had]; iexact Hd
  ihave Hs2 : (s ↦□ RaftRPC.mk t : IProp GF) $$ []
  · iexact Hs
  iStructNamed Hs2
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  wp_auto
  wp_apply (wp_deliver t γ snapP i W C _ _ false
      (github_com.hashicorp.raft.rpcRespP github_com.hashicorp.raft.RequestPreVoteResponse.ty
        (fun q => iprop(∃ rp : github_com.hashicorp.raft.RequestPreVoteResponse, q ↦ rp ∗
          github_com.hashicorp.raft.pvResp γ rp T)))) $$ [$Ht Hp]
    as %res %err ⟨%r, ⟨%Hres, %Herr⟩, HQ⟩
  · iintro %ch %γc #Hb
    isplit
    · unfold github_com.hashicorp.raft.rpcP
      ileft
      isplitr
      · ipureintro; rfl
      iright; iright; ileft
      iexists p, _, c, T, γc
      iframe Hp Hb
      isplitr
      · ipureintro; rfl
      unfold github_com.hashicorp.raft.pvReq github_com.hashicorp.raft.hdrOk
      iframe Hi' Hd'
      ipureintro
      refine ⟨?_, ?_⟩
      · rw [hwT]; exact hT
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
    iexists _, ⟨true, msg, ⟨(zeroValDef : PreVoteResp).Hdr'.ProtocolVersion', [], []⟩,
      (zeroValDef : PreVoteResp).Term', (zeroValDef : PreVoteResp).Granted'⟩
    iframe Hrep
    unfold preVoteRespOwn hdrOwn pvRespW
    isplitr
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownSlice_nil
      · iapply ownSlice_nil
    · ileft; ipureintro; rfl
  · rw [Hen, Hrq]
    wp_auto
    iunfold github_com.hashicorp.raft.pvResp at Hrv
    icases Hrv with ⟨Hterm, ⟨%snd, Hh⟩⟩
    iunfold github_com.hashicorp.raft.hdrOk at Hh
    icases Hh with ⟨%Hpv3, #Hid0, #Had0⟩
    wp_apply wp_toPreVoteResp $$ [$Hq $Hid0 $Had0] as %i1 %d1 ⟨Hq, -, -, Hi1, Hd1⟩
    (try wp_auto)
    iapply HΦ
    iexists _, ⟨false, [], ⟨rp.RPCHeader'.ProtocolVersion', snd, snd⟩, rp.Term', rp.Granted'⟩
    iframe Hrep
    unfold preVoteRespOwn hdrOwn pvRespW
    isplitl [Hi1 Hd1]
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitr
      · ipureintro; rfl
      iframe Hi1 Hd1
    · iright
      isplitr
      · ipureintro; rfl
      iframe Hterm
      ipureintro
      exact ⟨snd, Hpv3, rfl, rfl⟩

end proof

end Perennial
