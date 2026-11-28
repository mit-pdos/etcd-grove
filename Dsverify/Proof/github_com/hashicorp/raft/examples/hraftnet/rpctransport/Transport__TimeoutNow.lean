/-
The proof of `rpctransport.Transport.TimeoutNow`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__TimeoutNow
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__send
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.TimeoutReqBound
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

theorem raftSvc_TimeoutNow (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF)
    (j : github_com.hashicorp.raft.proto.SID) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    raftSvc (GF := GF) γ snapP j go!"TimeoutNow" bs Φ ⊣⊢
      iprop(∃ (h : HdrV) (c : github_com.hashicorp.raft.proto.SID),
        ⌜bs = encTimeoutReq h ∧ tnReqW h c⌝ ∗
        answers (fun rep => iprop(∃ r : TimeoutRespV, ⌜rep = encTimeoutResp r⌝)) Φ) := by
  unfold raftSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  exact .rfl

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.TimeoutNow.wp_proof
    (wp_send : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec (GF := GF) (hG := hG))
    (wp_toHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec (GF := GF) (hG := hG))
    (wp_fromHeader : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromHeader.spec (GF := GF) (hG := hG))
    (wp_TimeoutReqBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.TimeoutReqBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.TimeoutNow.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C id j args resp rq rp0 dq c
  wp_start as ⟨#Ht, Hargs, Hrq, Hresp⟩
  ihave #Ht2 := Ht
  iunfold isTrans at Ht2
  iNamed Ht2
  iunfold github_com.hashicorp.raft.tnReq at Hrq
  iunfold github_com.hashicorp.raft.hdrOk at Hrq
  icases Hrq with ⟨%Hpv, #Hid, #Had⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hargs
  iStructNamed Hargs
  wp_auto
  wp_apply wp_toHeader rq.RPCHeader' DfracDiscarded DfracDiscarded c c $$ [$Hid $Had] as %si %sa ⟨-, -, Hsi, Hsa⟩
  ihave Hargs : (args ↦{dq} rq : IProp GF) $$ [RPCHeader]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  (try wp_auto)
  wp_apply wp_TimeoutReqBound «$r0_ptr» (DFrac.own 1) _ (DFrac.own 1) c c $$ [$«$r0» $Hsi $Hsa] as %r ⟨%Hr, Hw, Hsi, Hsa⟩
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
    (try wp_auto)
    iapply HΦ
    iframe Hargs
    iright
    iframe Hresp
    iapply errStr_intro $$ HE
  (try wp_auto)
  wp_apply (wp_send t γ snapP i W C j go!"TimeoutNow" _ _
      (okAns (fun rep => iprop(∃ r : TimeoutRespV, ⌜rep = encTimeoutResp r⌝))) iprop(True)
      iprop(«$r0_ptr» ↦ (_root_.Perennial.zero_val TimeoutResp))
      (fun _ _ => iprop(∃ (w' : TimeoutResp) (r : TimeoutRespV), «$r0_ptr» ↦ w' ∗
        timeoutRespOwn w' (DFrac.own 1) r)))
    $$ [$Ht $«$r0» Hw Hsi Hsa] as %err Herr
  · isplitr
    · ipureintro
      refine ⟨by decide, by decide, by simp [interface.mkOk]⟩
    isplitl
    · iapply (Hlaws.enc_TimeoutReq _ (DFrac.own 1) (TimeoutReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' si sa)) ⟨rq.RPCHeader'.ProtocolVersion', c, c⟩)
      iframe Hw
      isplitl [Hsi Hsa]
      · simp only [hdrOwn]; iframe Hsi Hsa
      · iintro - -
        isplitr
        · ipureintro
          apply encTimeoutReq_length
          show timeoutBoundN c c ≤ maxReqN
          rw [← Hr]
          unfold maxReqN
          word
        isplitl
        · iapply (raftSvc_TimeoutNow γ snapP j _ _).2
          iexists ⟨rq.RPCHeader'.ProtocolVersion', c, c⟩, c
          isplitr
          · ipureintro; exact ⟨rfl, Hpv, rfl, rfl⟩
          iapply answers_okAns
        · itrivial
    · imodintro
      iintro HD %rep Hrep
      iunfold okAns at Hrep
      icases Hrep with (%Hne | ⟨%r, %Hrep⟩)
      · exfalso; exact Hne rfl
      · subst Hrep
        iapply (Hlaws.dec_TimeoutResp _ r)
        iframe HD
        iintro %w' Hw' Hown
        iexists w', r
        iframe
  icases Herr with (⟨%He, %rep, %w', %r, Hrep, Hown⟩ | #He)
  · subst He
    wp_auto
    iunfold timeoutRespOwn at Hown
    icases Hown with ⟨%Hfe, Hhdr⟩
    obtain ⟨Hf, He2⟩ := Hfe
    (try wp_auto)
    rw [Hf]
    cases hfl : r.failed
    · iunfold hdrOwn at Hhdr
      icases Hhdr with ⟨%Hpv2, Hid2, Had2⟩
      wp_auto
      wp_apply wp_fromHeader $$ [$Hid2 $Had2] as %a2 %b2 -
      (try wp_auto)
      iapply HΦ
      iframe Hargs
      ileft
      isplitr; · ipureintro; rfl
      iexists _
      iframe
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
