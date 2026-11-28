/-
The proof of `rpctransport.RaftRPC.InstallSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC__InstallSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromSnapReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.NewReader
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__deliver
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapResp

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.InstallSnapshot.wp_proof
    (wp_fromSnapReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromSnapReq.spec (GF := GF) (hG := hG))
    (wp_NewReader : github_com.hashicorp.raft.examples.snapstore.NewReader.spec (GF := GF) (hG := hG))
    (wp_deliver : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec (GF := GF) (hG := hG))
    (wp_toSnapResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapResp.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.InstallSnapshot.spec (GF := GF) (hG := hG) := by
  intro s γ snapP i W C args reply w v snd T s0 st
  wp_start as ⟨#Hr, Hargs, Hown, Hreq, Hrep⟩
  iunfold isRcv at Hr
  icases Hr with ⟨%t, #Hs, #Ht⟩
  unfold snapReqOwn hdrOwn
  icases Hown with ⟨%Hw, ⟨%Hpv, Hid, Had⟩, Hld, Hpe, Hcf, Hda⟩
  wp_auto
  wp_apply wp_fromSnapReq $$ [$Hargs $Hid $Had $Hld $Hpe $Hcf] as %p ⟨Hargs, Hid, Had, Hld, Hpe, Hcf, %i0, %d0, %c0, %c1, %c2, Hp, Hi0, Hd0, Hc0, Hc1, Hc2⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hss : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore $$ []
  · iPkgInit
  ihave #Heofv := io.eof_of_init $$ Hio
  iunfold errors.newVar at Heofv
  icases Heofv with ⟨%ex, #Heof, -, -⟩
  wp_apply wp_NewReader $$ [$Hss $Heof $Hda] as %rd ⟨Hda, %R, #Hrc, HR, %Hwt⟩
  iStructNamed Hs
  wp_auto
  unfold isReqW
  icases Hreq with ⟨%Hv, ⟨%ss, %Hcfg, #Hsc⟩, #Hli, #Hav, HsP⟩
  obtain ⟨HvT, HvI, HvL, HvV, HvS, Hsnd, Hs1, ⟨Hhpv, Hhid, Hhad⟩, Hvld, Hvlen⟩ := Hv
  obtain ⟨HwV, HwT, HwI, HwL, HwC, HwS⟩ := Hw
  ipersist Hi0
  ipersist Hd0
  ipersist Hc0
  ipersist Hc1
  ipersist Hc2
  wp_apply wp_deliver t γ snapP i W C (interface.mkOk (go.GoType.PointerType github_com.hashicorp.raft.InstallSnapshotRequest.ty) #p)
      (interface.mkOk (go.GoType.PointerType github_com.hashicorp.raft.examples.snapstore.Reader.ty) #rd) false
      (github_com.hashicorp.raft.rpcRespAnyP github_com.hashicorp.raft.InstallSnapshotResponse.ty
        (fun q => iprop(∃ rp : github_com.hashicorp.raft.InstallSnapshotResponse, q ↦ rp ∗ github_com.hashicorp.raft.isResp γ rp)))
      $$ [$Ht Hp HR HsP] as %res %err ⟨%r, ⟨%Hres, %Herr⟩, Hq⟩
  · iintro %ch %γc #Hbag
    isplit
    · unfold github_com.hashicorp.raft.rpcP
      iright
      unfold github_com.hashicorp.raft.isRpcP
      iexists p, _, snd, T, s0, st, v.data, ⟨go.GoType.PointerType github_com.hashicorp.raft.examples.snapstore.Reader.ty, #rd⟩, γc
      iframe Hp Hbag
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr [HR HsP]
      · unfold github_com.hashicorp.raft.isReq github_com.hashicorp.raft.hdrOk
        simp only
        iframe Hli Hav
        isplitr
        · ipureintro
          refine ⟨?_, ?_, ?_, ?_, ?_, Hsnd, Hs1⟩
          · rw [HwT]; exact HvT
          · rw [HwI]; exact HvI
          · rw [HwL]; exact HvL
          · rw [HwV]; exact HvV
          · rw [HwS]; exact HvS
        isplitr
        · rw [Hpv, Hhpv, ← Hhid]
          iframe Hi0
          rw [Hhid, ← Hhad]
          iframe Hd0
          ipureintro; trivial
        isplitr
        · rw [← Hvld]; iexact Hc0
        isplitr
        · iexists v.peers; iexact Hc1
        iexists ss
        rw [HwC, ← Hcfg]
        iframe Hc2 Hsc
      · unfold github_com.hashicorp.raft.snapStream
        iexists R, _
        unfold github_com.hashicorp.raft.readCloserOk
        icases Hrc with ⟨#Hsr, -⟩
        iframe Hsr HR Heof HsP
        ipureintro; exact ⟨Hwt, Hvlen⟩
    · iintro %Hf; exact absurd Hf (by simp)
  unfold github_com.hashicorp.raft.rpcRespAnyP
  icases Hq with (%Hne | ⟨%q, ⟨%He, %Hr⟩, %rp, Hq, Hrp⟩)
  · rcases err with ei | _
    · wp_auto
      simp only [installFailed]
      wp_auto
      iapply HΦ
      iexists _, ⟨true, go!"rpctransport: snapshot install failed", ⟨W64 0, [], []⟩, W64 0, false⟩
      iframe Hrep
      unfold snapRespOwn hdrOwn isRespW
      isplitr
      · isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        isplitr
        · ipureintro; rfl
        isplitl
        · iapply ownSlice_nil
        · iapply ownSlice_nil
      · ileft; ipureintro; rfl
    · exfalso; exact Hne Herr
  · rw [Herr] at He
    rw [Hres] at Hr
    subst He Hr
    wp_auto
    unfold github_com.hashicorp.raft.isResp
    icases Hrp with ⟨#Hterm, %id, %ad, #Hid, #Had⟩
    wp_apply wp_toSnapResp $$ [$Hq $Hid $Had] as %i1 %d1 ⟨Hq, -, -, Hi1, Hd1⟩
    iapply HΦ
    iexists _, ⟨false, [], ⟨rp.RPCHeader'.ProtocolVersion', id, ad⟩, rp.Term', rp.Success'⟩
    iframe Hrep
    unfold snapRespOwn hdrOwn isRespW
    isplitl [Hi1 Hd1]
    · isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitr
      · ipureintro; rfl
      iframe Hi1 Hd1
    · iright
      isplitr
      · ipureintro; rfl
      iexact Hterm

end proof

end Perennial
