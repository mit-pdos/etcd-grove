/-
The proof of `rpctransport.RaftRPC.AppendEntries`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__AppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.isHeartbeat
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__deliver
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Ents

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


theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.AppendEntries.wp_proof
    (wp_fromAppendReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendReq.spec (GF := GF) (hG := hG))
    (wp_toAppendResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendResp.spec (GF := GF) (hG := hG))
    (wp_isHeartbeat : github_com.hashicorp.raft.examples.hraftnet.rpctransport.isHeartbeat.spec (GF := GF) (hG := hG))
    (wp_deliver : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.AppendEntries.spec (GF := GF) (hG := hG) := by
  intro s γ snapP i W C args reply w v snd T prev pt ents lci ss
  wp_start as ⟨#Hs, Hargs, Hown, Hreq, Hrep⟩
  unfold isRcv
  icases Hs with ⟨%t, #Hs, #Ht⟩
  unfold aeReqOwn hdrOwn
  icases Hown with ⟨%Hw, ⟨%Hpv, Hid, Had⟩, Hld, Hents⟩
  unfold aeReqW
  icases Hreq with ⟨%Hv, Hval, Hhist⟩
  obtain ⟨hT, hprev, hpt, hlci, ⟨hpv3, hid, had⟩, hld, hm⟩ := Hv
  obtain ⟨hwT, hwprev, hwpt, hwlci⟩ := Hw
  wp_auto
  wp_apply wp_fromAppendReq $$ [$Hargs $Hid $Had $Hld $Hents] as %p ⟨Hargs, Hid, Had, Hld, Hents, %i0, %d0, %c0, %es, Hp, Hi, Hd, Hc, Hes⟩
  ipersist Hi
  ipersist Hd
  ipersist Hc
  ihave #Hi' : (i0 ↦*□ snd : IProp GF) $$ [Hi]
  · rw [← hid]; iexact Hi
  ihave #Hd' : (d0 ↦*□ snd : IProp GF) $$ [Hd]
  · rw [← had]; iexact Hd
  ihave #Hc' : (c0 ↦*□ snd : IProp GF) $$ [Hc]
  · rw [← hld]; iexact Hc
  ihave Hes' := logsOwn_logPtrs es v.ents prev ents hm $$ Hes
  imod Hes' with ⟨%ptrs, #Hptrs, %Hplen, Hlp⟩
  ihave Hs2 : (s ↦□ RaftRPC.mk t : IProp GF) $$ []
  · iexact Hs
  iStructNamed Hs2
  (try (irename : ("_" ∷ True : IProp GF) => Hjunk; iclear Hjunk))
  (try wp_auto)
  wp_apply wp_isHeartbeat $$ [$Hp $Hd' $Hc' $Hptrs] as %b ⟨Hp, -, -, -, %Hb⟩
  (try wp_auto)
  have hnums : uint.nat w.Term' = T ∧ uint.nat w.PrevLogEntry' = prev ∧ uint.nat w.PrevLogTerm' = pt ∧
      uint.nat w.LeaderCommitIndex' = lci := by
    rw [hwT, hwprev, hwpt, hwlci]; exact ⟨hT, hprev, hpt, hlci⟩
  have hpvw : w.Hdr'.ProtocolVersion' = W64 3 := by rw [Hpv]; exact hpv3
  wp_apply (wp_deliver t γ snapP i W C _ _ b
      (github_com.hashicorp.raft.rpcRespP github_com.hashicorp.raft.AppendEntriesResponse.ty
        (fun q => iprop(∃ rp : github_com.hashicorp.raft.AppendEntriesResponse, q ↦ rp ∗
          github_com.hashicorp.raft.aeResp γ rp i T (prev + ents.length)
            (github_com.hashicorp.raft.isHb prev ents lci) ss)))) $$ [$Ht Hp Hlp Hval Hhist]
    as %res %err ⟨%r, ⟨%Hres, %Herr⟩, HQ⟩
  · iintro %ch %γc #Hb
    isplit
    · unfold github_com.hashicorp.raft.rpcP
      ileft
      isplitr
      · ipureintro; rfl
      ileft
      unfold github_com.hashicorp.raft.aeRpcP
      iexists p, _, snd, T, prev, pt, ents, lci, ss, γc
      iframe Hp Hb
      isplitr
      · ipureintro; rfl
      unfold github_com.hashicorp.raft.aeReq github_com.hashicorp.raft.hdrOk
      iframe Hi' Hd' Hc' Hval Hhist
      isplitr
      · ipureintro; exact hnums
      isplitr
      · ipureintro; exact hpvw
      iexists ptrs
      iframe Hptrs Hlp
      ipureintro; exact Hplen
    · iintro %Hbt
      obtain ⟨h0, hp0, hl0⟩ := Hb Hbt
      simp only at h0 hl0
      have hprev0 : prev = 0 := by rw [← hnums.2.1, h0]; rfl
      have hlci0 : lci = 0 := by rw [← hnums.2.2.2, hl0]; rfl
      have hents0 : ents = [] := by
        subst hp0; exact List.eq_nil_of_length_eq_zero (by simpa using Hplen.symm)
      subst hprev0 hlci0 hents0 hp0
      unfold github_com.hashicorp.raft.hbRpcP
      isplitr
      · ipureintro; rfl
      iexists p, _, snd, T, pt, 0, ss, γc
      iframe Hp Hb
      isplitr
      · ipureintro; rfl
      isplitl
      · unfold github_com.hashicorp.raft.aeReq github_com.hashicorp.raft.hdrOk
        iframe Hi' Hd' Hc' Hval Hhist
        isplitr
        · ipureintro; exact hnums
        isplitr
        · ipureintro; exact hpvw
        iexists []
        iframe Hptrs Hlp
        ipureintro; rfl
      ipureintro; rfl
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
    iexists _, ⟨true, msg, ⟨(zeroValDef : AppendResp).Hdr'.ProtocolVersion', [], []⟩,
      (zeroValDef : AppendResp).Term', (zeroValDef : AppendResp).LastLog',
      (zeroValDef : AppendResp).Success', (zeroValDef : AppendResp).NoRetryBackoff'⟩
    iframe Hrep
    unfold aeRespOwn hdrOwn aeRespW
    isplitr
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownSlice_nil
      · iapply ownSlice_nil
    · ileft; ipureintro; rfl
  · rw [Hen, Hrq]
    wp_auto
    iunfold github_com.hashicorp.raft.aeResp at Hrv
    icases Hrv with ⟨Hterm, Hg, ⟨%snd', Hh⟩⟩
    iunfold github_com.hashicorp.raft.hdrOk at Hh
    icases Hh with ⟨%Hpv3, #Hid0, #Had0⟩
    wp_apply wp_toAppendResp $$ [$Hq $Hid0 $Had0] as %i1 %d1 ⟨Hq, -, -, Hi1, Hd1⟩
    (try wp_auto)
    iapply HΦ
    iexists _, ⟨false, [], ⟨rp.RPCHeader'.ProtocolVersion', snd', snd'⟩, rp.Term', rp.LastLog',
      rp.Success', rp.NoRetryBackoff'⟩
    iframe Hrep
    unfold aeRespOwn hdrOwn aeRespW
    isplitl [Hi1 Hd1]
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      isplitr
      · ipureintro; rfl
      iframe Hi1 Hd1
    · iright
      isplitr
      · ipureintro; rfl
      iframe Hterm Hg
      ipureintro
      exact ⟨snd', Hpv3, rfl, rfl⟩

end proof

end Perennial
