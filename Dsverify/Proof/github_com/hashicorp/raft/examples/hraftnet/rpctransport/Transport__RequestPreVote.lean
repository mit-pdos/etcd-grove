/-
The proof of `rpctransport.Transport.RequestPreVote`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__RequestPreVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__send
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toPreVoteReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.PreVoteReqBound
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

theorem raftSvc_RequestPreVote (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF)
    (j : github_com.hashicorp.raft.proto.SID) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    raftSvc (GF := GF) γ snapP j go!"RequestPreVote" bs Φ ⊣⊢
      iprop(∃ (v : PreVoteReqV) (c : github_com.hashicorp.raft.proto.SID) (T : Nat),
        ⌜bs = encPreVoteReq v ∧ pvReqW v c T⌝ ∗
        answers (fun rep => iprop(∃ r : PreVoteRespV, ⌜rep = encPreVoteResp r⌝ ∗ pvRespW γ r T)) Φ) := by
  unfold raftSvc
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  exact .rfl

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.RequestPreVote.wp_proof
    (wp_send : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec (GF := GF) (hG := hG))
    (wp_toPreVoteReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toPreVoteReq.spec (GF := GF) (hG := hG))
    (wp_fromPreVoteResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteResp.spec (GF := GF) (hG := hG))
    (wp_PreVoteReqBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.PreVoteReqBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.RequestPreVote.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C id j args resp rq rp0 dq c T
  wp_start as ⟨#Ht, Hargs, Hrq, Hresp⟩
  ihave #Ht2 := Ht
  iunfold isTrans at Ht2
  iNamed Ht2
  iunfold github_com.hashicorp.raft.pvReq at Hrq
  icases Hrq with ⟨%HT, Hh⟩
  iunfold github_com.hashicorp.raft.hdrOk at Hh
  icases Hh with ⟨%Hpv, #Hid, #Had⟩
  (try wp_auto)
  wp_apply wp_toPreVoteReq args dq rq DfracDiscarded c c $$ [$Hargs $Hid $Had] as %wl ⟨Hargs, -, -, %si, %sa, Hw, Hsi, Hsa⟩
  (try wp_auto)
  wp_apply wp_PreVoteReqBound wl (DFrac.own 1) _ (DFrac.own 1) c c $$ [$Hw $Hsi $Hsa] as %r ⟨%Hr, Hw, Hsi, Hsa⟩
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
    (try wp_auto)
    iapply HΦ
    iframe Hargs
    iright
    iframe Hresp
    iapply errStr_intro $$ HE
  (try wp_auto)
  wp_apply (wp_send t γ snapP i W C j go!"RequestPreVote" _ _
      (okAns (fun rep => iprop(∃ r : PreVoteRespV, ⌜rep = encPreVoteResp r⌝ ∗ pvRespW γ r T))) iprop(True)
      iprop(«$r0_ptr» ↦ (_root_.Perennial.zero_val PreVoteResp))
      (fun _ _ => iprop(∃ (w' : PreVoteResp) (r : PreVoteRespV), «$r0_ptr» ↦ w' ∗
        preVoteRespOwn w' (DFrac.own 1) r ∗ pvRespW γ r T)))
    $$ [$Ht $«$r0» Hw Hsi Hsa] as %err Herr
  · isplitr
    · ipureintro
      refine ⟨by decide, by decide, by simp [interface.mkOk]⟩
    isplitl
    · iapply (Hlaws.enc_PreVoteReq _ (DFrac.own 1)
        (PreVoteReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' si sa) rq.Term' rq.LastLogIndex' rq.LastLogTerm')
        ⟨⟨rq.RPCHeader'.ProtocolVersion', c, c⟩, rq.Term', rq.LastLogIndex', rq.LastLogTerm'⟩)
      iframe Hw
      isplitl [Hsi Hsa]
      · simp only [preVoteReqOwn, hdrOwn]; iframe Hsi Hsa; ipureintro; simp
      · iintro - -
        isplitr
        · ipureintro
          apply encPreVoteReq_length
          show preVoteBoundN c c ≤ maxReqN
          rw [← Hr]
          unfold maxReqN
          word
        isplitl
        · iapply (raftSvc_RequestPreVote γ snapP j _ _).2
          iexists ⟨⟨rq.RPCHeader'.ProtocolVersion', c, c⟩, rq.Term', rq.LastLogIndex', rq.LastLogTerm'⟩, c, T
          isplitr
          · ipureintro; exact ⟨rfl, HT, Hpv, rfl, rfl⟩
          iapply answers_okAns
        · itrivial
    · imodintro
      iintro HD %rep Hrep
      iunfold okAns at Hrep
      icases Hrep with (%Hne | ⟨%r, %Hrep, HR⟩)
      · exfalso; exact Hne rfl
      · subst Hrep
        iapply (Hlaws.dec_PreVoteResp _ r)
        iframe HD
        iintro %w' Hw' Hown
        iexists w', r
        iframe
  icases Herr with (⟨%He, %rep, %w', %r, Hrep, Hown, HR⟩ | #He)
  · subst He
    wp_auto
    iunfold preVoteRespOwn at Hown
    icases Hown with ⟨%Hfe, Hhdr⟩
    obtain ⟨Hf, He2, HTe, HGr⟩ := Hfe
    (try wp_auto)
    rw [Hf]
    cases hfl : r.failed
    · iunfold pvRespW at HR
      icases HR with (%Hft | ⟨-, HRt, %Hsnd⟩)
      · exfalso; rw [hfl] at Hft; exact Bool.false_ne_true Hft
      obtain ⟨snd, Hpv2, Hid2, Had2⟩ := Hsnd
      iunfold hdrOwn at Hhdr
      icases Hhdr with ⟨%Hpv3, Hi2, Ha2⟩
      iapply wp_fupd
      wp_auto
      wp_apply wp_fromPreVoteResp $$ [$Hrep $Hi2 $Ha2] as %a2 %b2 ⟨-, -, -, Hi3, Ha3⟩
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
      simp only [github_com.hashicorp.raft.pvResp, github_com.hashicorp.raft.hdrOk]
      rw [HTe, Hpv3, Hpv2]
      iframe HRt
      iexists snd
      rw [← Hid2, Hid2.trans Had2.symm]
      iframe Hi3 Ha3
      ipureintro; rfl
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
