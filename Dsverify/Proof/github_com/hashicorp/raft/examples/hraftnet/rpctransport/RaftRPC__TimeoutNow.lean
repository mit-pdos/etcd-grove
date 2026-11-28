/-
The proof of `rpctransport.RaftRPC.TimeoutNow`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__TimeoutNow
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader
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


theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.TimeoutNow.wp_proof
    (wp_fromHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader.spec (GF := GF) (hG := hG))
    (wp_toHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec (GF := GF) (hG := hG))
    (wp_deliver : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.TimeoutNow.spec (GF := GF) (hG := hG) := by
  intro s γ snapP i W C args reply w h c
  wp_start as ⟨#Hs, Hargs, Hown, %Hv, Hrep⟩
  unfold isRcv
  icases Hs with ⟨%t, #Hs, #Ht⟩
  unfold hdrOwn
  icases Hown with ⟨%Hpv, Hid, Had⟩
  unfold tnReqW hdrIs at Hv
  obtain ⟨hpv3, hid, had⟩ := Hv
  wp_auto
  wp_apply wp_fromHeader $$ [$Hid $Had] as %i0 %d0 ⟨Hid, Had, Hi, Hd⟩
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
  (try wp_auto)
  wp_alloc p as Hp
  (try wp_auto)
  wp_apply (wp_deliver t γ snapP i W C _ _ false
      (github_com.hashicorp.raft.rpcRespOkP github_com.hashicorp.raft.TimeoutNowResponse.ty
        (fun q => iprop(∃ rp : github_com.hashicorp.raft.TimeoutNowResponse, q ↦ rp ∗
          ∃ id ad : List w8, rp.RPCHeader'.ID' ↦*□ id ∗ rp.RPCHeader'.Addr' ↦*□ ad)))) $$ [$Ht Hp]
    as %res %err ⟨%r, ⟨%Hres, %Herr⟩, HQ⟩
  · iintro %ch %γc #Hb
    isplit
    · unfold github_com.hashicorp.raft.rpcP
      ileft
      isplitr
      · ipureintro; rfl
      iright; iright; iright
      iexists p, _, c, γc
      iframe Hp Hb
      isplitr
      · ipureintro; rfl
      unfold github_com.hashicorp.raft.tnReq github_com.hashicorp.raft.hdrOk
      iframe Hi' Hd'
      ipureintro
      rw [Hpv]; exact hpv3
    · iintro %Hf
      exact absurd Hf (by decide)
  subst Herr Hres
  unfold github_com.hashicorp.raft.rpcRespOkP
  icases HQ with ⟨%q, ⟨%Hen, %Hrq⟩, %rp, Hq, %id1, %ad1, #Hid1, #Had1⟩
  rw [Hen, Hrq]
  wp_auto
  wp_apply wp_toHeader $$ [$Hid1 $Had1] as %i1 %d1 ⟨-, -, Hi1, Hd1⟩
  (try wp_auto)
  iapply HΦ
  iexists _, ⟨(zeroValDef : TimeoutResp).Failed', (zeroValDef : TimeoutResp).Err', ⟨rp.RPCHeader'.ProtocolVersion', id1, ad1⟩⟩
  iframe Hrep
  unfold timeoutRespOwn hdrOwn
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · ipureintro; rfl
  iframe Hi1 Hd1

end proof

end Perennial
