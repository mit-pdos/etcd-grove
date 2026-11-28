/-
The proof of `rpctransport.Transport.InstallSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__InstallSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__send
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromSnapResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.SnapReqBound
public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.ReadAll
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireLen
public import Perennial.Proof.errors.NewVar

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

set_option goose.wp.extras true

theorem raftSvc_InstallSnapshot (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF)
    (j : github_com.hashicorp.raft.proto.SID) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    raftSvc (GF := GF) γ snapP j go!"InstallSnapshot" bs Φ ⊣⊢
      iprop(∃ (v : SnapReqV) (snd : github_com.hashicorp.raft.proto.SID) (T s st : Nat),
        ⌜bs = encSnapReq v⌝ ∗ isReqW γ snapP v snd j T s st ∗
        answers (fun rep => iprop(∃ r : SnapRespV, ⌜rep = encSnapResp r⌝ ∗ isRespW γ r)) Φ) := by
  unfold raftSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  exact .rfl

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.InstallSnapshot.wp_proof
    (wp_send : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec (GF := GF) (hG := hG))
    (wp_toSnapReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapReq.spec (GF := GF) (hG := hG))
    (wp_fromSnapResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromSnapResp.spec (GF := GF) (hG := hG))
    (wp_SnapReqBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.SnapReqBound.spec (GF := GF) (hG := hG))
    (wp_ReadAll : github_com.hashicorp.raft.examples.snapstore.ReadAll.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.InstallSnapshot.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C id j args resp rq rp0 dq snd T s st b data
  wp_start as ⟨#Ht, Hargs, Hrq, Hresp, Hstream⟩
  ihave #Ht2 := Ht
  iunfold isTrans at Ht2
  iNamed Ht2
  iunfold github_com.hashicorp.raft.isReq at Hrq
  icases Hrq with ⟨%HT, Hh, #Hld, ⟨%pb, #Hpb⟩, ⟨%ss, #Hcfg, #HsC⟩, #HlI, #Hav⟩
  iunfold github_com.hashicorp.raft.hdrOk at Hh
  icases Hh with ⟨%Hpv, #Hid, #Had⟩
  iunfold github_com.hashicorp.raft.snapStream at Hstream
  icases Hstream with ⟨%R, %eof, #Hrd, HR, #Heof, -, HsnapP, %Hblen⟩
  ihave #Hsnap : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_ReadAll data R b eof $$ [$Hsnap $Heof $Hrd $HR] as %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_toSnapReq args dq rq DfracDiscarded snd snd snd pb (github_com.hashicorp.raft.encodeServers ss) sl
    $$ [$Hargs $Hid $Had $Hld $Hpb $Hcfg]
    as %wl ⟨Hargs, -, -, -, -, -, %si, %sa, %c0, %c1, %c2, Hw, Hsi, Hsa, Hc0, Hc1, Hc2⟩
  (try wp_auto)
  wp_apply wp_SnapReqBound wl (DFrac.own 1) _ (DFrac.own 1) snd snd snd pb (github_com.hashicorp.raft.encodeServers ss) b
    $$ [$Hw $Hsi $Hsa $Hc0 $Hc1 $Hc2 $Hsl] as %r ⟨%Hr, Hw, Hsi, Hsa, Hc0, Hc1, Hc2, Hsl⟩
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
    (try wp_auto)
    iapply HΦ
    iframe Hargs
    iright
    iframe Hresp
    iapply errStr_intro $$ HE
  (try wp_auto)
  wp_apply (wp_send t γ snapP i W C j go!"InstallSnapshot" _ _
      (okAns (fun rep => iprop(∃ r : SnapRespV, ⌜rep = encSnapResp r⌝ ∗ isRespW γ r))) iprop(True)
      iprop(«$r0_ptr» ↦ (_root_.Perennial.zero_val SnapResp))
      (fun _ _ => iprop(∃ (w' : SnapResp) (r : SnapRespV), «$r0_ptr» ↦ w' ∗
        snapRespOwn w' (DFrac.own 1) r ∗ isRespW γ r)))
    $$ [$Ht $«$r0» Hw Hsi Hsa Hc0 Hc1 Hc2 Hsl HsnapP] as %err Herr
  · isplitr
    · ipureintro
      refine ⟨by decide, by decide, by simp [interface.mkOk]⟩
    isplitl
    · iapply (Hlaws.enc_SnapReq _ (DFrac.own 1)
        (SnapReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' si sa) rq.SnapshotVersion' rq.Term' c0
          rq.LastLogIndex' rq.LastLogTerm' c1 c2 rq.ConfigurationIndex' rq.Size' sl)
        ⟨⟨rq.RPCHeader'.ProtocolVersion', snd, snd⟩, rq.SnapshotVersion', rq.Term', snd, rq.LastLogIndex',
          rq.LastLogTerm', pb, github_com.hashicorp.raft.encodeServers ss, rq.ConfigurationIndex', rq.Size', b⟩)
      iframe Hw
      isplitl [Hsi Hsa Hc0 Hc1 Hc2 Hsl]
      · simp only [snapReqOwn, hdrOwn]; iframe Hsi Hsa Hc0 Hc1 Hc2 Hsl; ipureintro; simp
      · iintro - -
        isplitr
        · ipureintro
          apply encSnapReq_length
          show snapBoundN snd snd snd pb (github_com.hashicorp.raft.encodeServers ss) b ≤ maxReqN
          rw [← Hr]
          unfold maxReqN
          word
        isplitl
        · iapply (raftSvc_InstallSnapshot γ snapP j _ _).2
          iexists ⟨⟨rq.RPCHeader'.ProtocolVersion', snd, snd⟩, rq.SnapshotVersion', rq.Term', snd,
            rq.LastLogIndex', rq.LastLogTerm', pb, github_com.hashicorp.raft.encodeServers ss,
            rq.ConfigurationIndex', rq.Size', b⟩, snd, T, s, st
          isplitr
          · ipureintro; rfl
          isplitl [HsnapP]
          · unfold isReqW
            iframe HlI Hav HsnapP
            isplitr
            · ipureintro
              obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := HT
              exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨Hpv, rfl, rfl⟩, rfl, Hblen⟩
            · iexists ss
              iframe HsC
              ipureintro; rfl
          iapply answers_okAns
        · itrivial
    · imodintro
      iintro HD %rep Hrep
      iunfold okAns at Hrep
      icases Hrep with (%Hne | ⟨%r, %Hrep, HR⟩)
      · exfalso; exact Hne rfl
      · subst Hrep
        iapply (Hlaws.dec_SnapResp _ r)
        iframe HD
        iintro %w' Hw' Hown
        iexists w', r
        iframe
  icases Herr with (⟨%He, %rep, %w', %r, Hrep, Hown, HR⟩ | #He)
  · subst He
    wp_auto
    iunfold snapRespOwn at Hown
    icases Hown with ⟨%Hfe, Hhdr⟩
    obtain ⟨Hf, He2, HTe, HSu⟩ := Hfe
    (try wp_auto)
    rw [Hf]
    cases hfl : r.failed
    · iunfold isRespW at HR
      icases HR with (%Hft | ⟨-, HRt⟩)
      · exfalso; rw [hfl] at Hft; exact Bool.false_ne_true Hft
      iunfold hdrOwn at Hhdr
      icases Hhdr with ⟨%Hpv3, Hi2, Ha2⟩
      iapply wp_fupd
      wp_auto
      wp_apply wp_fromSnapResp $$ [$Hrep $Hi2 $Ha2] as %a2 %b2 ⟨-, -, -, Hi3, Ha3⟩
      (try wp_auto)
      ipersist Hi3
      ipersist Ha3
      imodintro
      iapply HΦ
      iframe Hargs
      ileft
      isplitr; · ipureintro; rfl
      iexists _
      iframe
      simp only [github_com.hashicorp.raft.isResp]
      rw [HTe]
      iframe HRt
      iexists r.hdr.id, r.hdr.addr
      iframe Hi3 Ha3
    · wp_auto
      wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
      (try wp_auto)
      iapply HΦ
      iframe Hargs
      iright
      iframe Hresp
      iapply errStr_intro $$ HE
  · ihave #He2 := He
    iunfold errStr at He2
    icases He2 with ⟨%x, %msg, %Hex, -⟩
    subst Hex
    wp_auto
    iapply HΦ
    iframe Hargs
    iright
    iframe Hresp He

end proof

end Perennial
