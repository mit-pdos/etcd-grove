/-
The proof of `rpctransport.Transport.RequestVote`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__RequestVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__send
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromVoteResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.VoteReqBound
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

theorem raftSvc_RequestVote (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF)
    (j : github_com.hashicorp.raft.proto.SID) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    raftSvc (GF := GF) γ snapP j go!"RequestVote" bs Φ ⊣⊢
      iprop(∃ (v : VoteReqV) (c : github_com.hashicorp.raft.proto.SID) (T li lt : Nat),
        ⌜bs = encVoteReq v⌝ ∗ rvReqW γ v c T li lt ∗
        answers (fun rep => iprop(∃ r : VoteRespV, ⌜rep = encVoteResp r⌝ ∗ rvRespW γ r j c T)) Φ) := by
  unfold raftSvc
  rw [if_neg (by decide), if_pos rfl]
  exact .rfl

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.RequestVote.wp_proof
    (wp_send : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec (GF := GF) (hG := hG))
    (wp_toVoteReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toVoteReq.spec (GF := GF) (hG := hG))
    (wp_fromVoteResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromVoteResp.spec (GF := GF) (hG := hG))
    (wp_VoteReqBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.VoteReqBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.RequestVote.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C id j args resp rq rp0 dq c T li lt
  wp_start as ⟨#Ht, Hargs, Hrq, Hresp⟩
  ihave #Ht2 := Ht
  iunfold isTrans at Ht2
  iNamed Ht2
  iunfold github_com.hashicorp.raft.rvReq at Hrq
  icases Hrq with ⟨%HT, Hh, #Hcand, #HcI⟩
  iunfold github_com.hashicorp.raft.hdrOk at Hh
  icases Hh with ⟨%Hpv, #Hid, #Had⟩
  (try wp_auto)
  wp_apply wp_toVoteReq args dq rq DfracDiscarded c c c $$ [$Hargs $Hid $Had $Hcand] as %wl ⟨Hargs, -, -, -, %si, %sa, %sc, Hw, Hsi, Hsa, Hsc⟩
  (try wp_auto)
  wp_apply wp_VoteReqBound wl (DFrac.own 1) _ (DFrac.own 1) c c c $$ [$Hw $Hsi $Hsa $Hsc] as %r ⟨%Hr, Hw, Hsi, Hsa, Hsc⟩
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
    (try wp_auto)
    iapply HΦ
    iframe Hargs
    iright
    iframe Hresp
    iapply errStr_intro $$ HE
  (try wp_auto)
  wp_apply (wp_send t γ snapP i W C j go!"RequestVote" _ _
      (okAns (fun rep => iprop(∃ r : VoteRespV, ⌜rep = encVoteResp r⌝ ∗ rvRespW γ r j c T))) iprop(True)
      iprop(«$r0_ptr» ↦ (_root_.Perennial.zero_val VoteResp))
      (fun _ _ => iprop(∃ (w' : VoteResp) (r : VoteRespV), «$r0_ptr» ↦ w' ∗
        voteRespOwn w' (DFrac.own 1) r ∗ rvRespW γ r j c T)))
    $$ [$Ht $«$r0» Hw Hsi Hsa Hsc] as %err Herr
  · isplitr
    · ipureintro
      refine ⟨by decide, by decide, by simp [interface.mkOk]⟩
    isplitl
    · iapply (Hlaws.enc_VoteReq _ (DFrac.own 1)
        (VoteReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' si sa) rq.Term' sc rq.LastLogIndex' rq.LastLogTerm'
          rq.LeadershipTransfer')
        ⟨⟨rq.RPCHeader'.ProtocolVersion', c, c⟩, rq.Term', c, rq.LastLogIndex', rq.LastLogTerm',
          rq.LeadershipTransfer'⟩)
      iframe Hw
      isplitl [Hsi Hsa Hsc]
      · simp only [voteReqOwn, hdrOwn]; iframe Hsi Hsa Hsc; ipureintro; simp
      · iintro - -
        isplitr
        · ipureintro
          apply encVoteReq_length
          show voteBoundN c c c ≤ maxReqN
          rw [← Hr]
          unfold maxReqN
          word
        isplitl
        · iapply (raftSvc_RequestVote γ snapP j _ _).2
          iexists ⟨⟨rq.RPCHeader'.ProtocolVersion', c, c⟩, rq.Term', c, rq.LastLogIndex', rq.LastLogTerm',
            rq.LeadershipTransfer'⟩, c, T, li, lt
          isplitr
          · ipureintro; rfl
          isplitr
          · unfold rvReqW
            iframe HcI
            ipureintro
            obtain ⟨h1, h2, h3⟩ := HT
            exact ⟨h1, h2, h3, ⟨Hpv, rfl, rfl⟩, rfl⟩
          iapply answers_okAns
        · itrivial
    · imodintro
      iintro HD %rep Hrep
      iunfold okAns at Hrep
      icases Hrep with (%Hne | ⟨%r, %Hrep, HR⟩)
      · exfalso; exact Hne rfl
      · subst Hrep
        iapply (Hlaws.dec_VoteResp _ r)
        iframe HD
        iintro %w' Hw' Hown
        iexists w', r
        iframe
  icases Herr with (⟨%He, %rep, %w', %r, Hrep, Hown, HR⟩ | #He)
  · subst He
    wp_auto
    iunfold voteRespOwn at Hown
    icases Hown with ⟨%Hfe, Hhdr, Hpe⟩
    obtain ⟨Hf, He2, HTe, HGr⟩ := Hfe
    (try wp_auto)
    rw [Hf]
    cases hfl : r.failed
    · iunfold rvRespW at HR
      icases HR with (%Hft | ⟨-, HRt, HRg, %Hsnd⟩)
      · exfalso; rw [hfl] at Hft; exact Bool.false_ne_true Hft
      obtain ⟨snd, Hpv2, Hid2, Had2⟩ := Hsnd
      iunfold hdrOwn at Hhdr
      icases Hhdr with ⟨%Hpv3, Hi2, Ha2⟩
      iapply wp_fupd
      wp_auto
      wp_apply wp_fromVoteResp $$ [$Hrep $Hi2 $Ha2 $Hpe] as %a2 %b2 %c2 ⟨-, -, -, -, Hi3, Ha3, Hc3⟩
      (try wp_auto)
      ipersist Hi3
      ipersist Ha3
      ipersist Hc3
      imodintro
      iapply HΦ
      iframe Hargs
      ileft
      isplitr; · ipureintro; rfl
      iexists _
      iframe
      simp only [github_com.hashicorp.raft.rvResp, github_com.hashicorp.raft.hdrOk]
      rw [HTe, HGr, Hpv3, Hpv2]
      iframe HRt HRg
      isplitr
      · iexists r.peers; iexact Hc3
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
