/-
The proof of `rpctransport.Transport.AppendEntries`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__AppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__send
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendReq
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendResp
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.AppendReqBound
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireLen
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Ents
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

theorem raftSvc_AppendEntries (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF)
    (j : github_com.hashicorp.raft.proto.SID) (bs : List w8) (Φ : List w8 → GoString → IProp GF) :
    raftSvc (GF := GF) γ snapP j go!"AppendEntries" bs Φ ⊣⊢
      iprop(∃ (v : AEReqV) (snd : github_com.hashicorp.raft.proto.SID) (T prev pt : Nat)
          (ents : github_com.hashicorp.raft.proto.RLog) (lci : Nat) (ss : github_com.hashicorp.raft.proto.Snap),
        ⌜bs = encAEReq v⌝ ∗ aeReqW γ v snd T prev pt ents lci ss ∗
        answers (fun rep => iprop(∃ r : AERespV, ⌜rep = encAEResp r⌝ ∗
          aeRespW γ r j T (prev + ents.length) (github_com.hashicorp.raft.isHb prev ents lci) ss)) Φ) := by
  unfold raftSvc
  rw [if_pos rfl]
  exact .rfl

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.AppendEntries.wp_proof
    (wp_send : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec (GF := GF) (hG := hG))
    (wp_toAppendReq : github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendReq.spec (GF := GF) (hG := hG))
    (wp_fromAppendResp : github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendResp.spec (GF := GF) (hG := hG))
    (wp_AppendReqBound : github_com.hashicorp.raft.examples.hraftnet.rpctransport.AppendReqBound.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.AppendEntries.spec (GF := GF) (hG := hG) := by
  intro t γ snapP i W C id j args resp rq rp0 dq snd T prev pt ents lci ss
  wp_start as ⟨#Ht, Hargs, Hrq, Hresp⟩
  ihave #Ht2 := Ht
  iunfold isTrans at Ht2
  iNamed Ht2
  iunfold github_com.hashicorp.raft.aeReq at Hrq
  icases Hrq with ⟨%HT, Hh, #Hld, ⟨%ptrs, #Hptrs, %Hplen, Hpl⟩, Hav, Hss⟩
  iunfold github_com.hashicorp.raft.hdrOk at Hh
  icases Hh with ⟨%Hpv, #Hid, #Had⟩
  ihave Hlg : (∃ vs : List EntV, logsOwn rq.Entries' DfracDiscarded vs ∗ ⌜entsMatch vs prev ents⌝ : IProp GF) $$ [Hpl]
  · iapply logPtrs_logsOwn; iframe Hptrs Hpl; ipureintro; exact Hplen
  icases Hlg with ⟨%vs, Hlogs, %Hm⟩
  (try wp_auto)
  wp_apply wp_toAppendReq args dq rq DfracDiscarded snd snd snd vs $$ [$Hargs $Hid $Had $Hld $Hlogs]
    as %wl ⟨Hargs, -, -, -, -, %si, %sa, %sl, %es, Hw, Hsi, Hsa, Hsl, Hes⟩
  (try wp_auto)
  wp_apply wp_AppendReqBound wl (DFrac.own 1) _ (DFrac.own 1) snd snd snd vs $$ [$Hw $Hsi $Hsa $Hsl $Hes]
    as %r ⟨%Hr, Hw, Hsi, Hsa, Hsl, Hes⟩
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x ⟨-, #HE⟩
    (try wp_auto)
    iapply HΦ
    iframe Hargs
    iright
    iframe Hresp
    iapply errStr_intro $$ HE
  (try wp_auto)
  wp_apply (wp_send t γ snapP i W C j go!"AppendEntries" _ _
      (okAns (fun rep => iprop(∃ r : AERespV, ⌜rep = encAEResp r⌝ ∗
        aeRespW γ r j T (prev + ents.length) (github_com.hashicorp.raft.isHb prev ents lci) ss))) iprop(True)
      iprop(«$r0_ptr» ↦ (_root_.Perennial.zero_val AppendResp))
      (fun _ _ => iprop(∃ (w' : AppendResp) (r : AERespV), «$r0_ptr» ↦ w' ∗
        aeRespOwn w' (DFrac.own 1) r ∗
        aeRespW γ r j T (prev + ents.length) (github_com.hashicorp.raft.isHb prev ents lci) ss)))
    $$ [$Ht $«$r0» Hw Hsi Hsa Hsl Hes Hav Hss] as %err Herr
  · isplitr
    · ipureintro
      refine ⟨by decide, by decide, by simp [interface.mkOk]⟩
    isplitl
    · iapply (Hlaws.enc_AppendReq _ (DFrac.own 1)
        (AppendReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' si sa) rq.Term' sl rq.PrevLogEntry'
          rq.PrevLogTerm' es rq.LeaderCommitIndex')
        ⟨⟨rq.RPCHeader'.ProtocolVersion', snd, snd⟩, rq.Term', snd, rq.PrevLogEntry', rq.PrevLogTerm', vs,
          rq.LeaderCommitIndex'⟩)
      iframe Hw
      isplitl [Hsi Hsa Hsl Hes]
      · simp only [aeReqOwn, hdrOwn]; iframe Hsi Hsa Hsl Hes; ipureintro; simp
      · iintro - -
        isplitr
        · ipureintro
          apply encAEReq_length
          show aeBoundN snd snd snd vs ≤ maxReqN
          rw [← Hr]
          unfold maxReqN
          word
        isplitl
        · iapply (raftSvc_AppendEntries γ snapP j _ _).2
          iexists ⟨⟨rq.RPCHeader'.ProtocolVersion', snd, snd⟩, rq.Term', snd, rq.PrevLogEntry', rq.PrevLogTerm', vs,
            rq.LeaderCommitIndex'⟩, snd, T, prev, pt, ents, lci, ss
          isplitr
          · ipureintro; rfl
          isplitl [Hav Hss]
          · unfold aeReqW
            iframe Hav Hss
            ipureintro
            obtain ⟨h1, h2, h3, h4⟩ := HT
            exact ⟨h1, h2, h3, h4, ⟨Hpv, rfl, rfl⟩, rfl, Hm⟩
          iapply answers_okAns
        · itrivial
    · imodintro
      iintro HD %rep Hrep
      iunfold okAns at Hrep
      icases Hrep with (%Hne | ⟨%r, %Hrep, HR⟩)
      · exfalso; exact Hne rfl
      · subst Hrep
        iapply (Hlaws.dec_AppendResp _ r)
        iframe HD
        iintro %w' Hw' Hown
        iexists w', r
        iframe
  icases Herr with (⟨%He, %rep, %w', %r, Hrep, Hown, HR⟩ | #He)
  · subst He
    wp_auto
    iunfold aeRespOwn at Hown
    icases Hown with ⟨%Hfe, Hhdr⟩
    obtain ⟨Hf, He2, HTe, HLL, HSu, HNR⟩ := Hfe
    (try wp_auto)
    rw [Hf]
    cases hfl : r.failed
    · iunfold aeRespW at HR
      icases HR with (%Hft | ⟨-, HRt, HRs, %Hsnd⟩)
      · exfalso; rw [hfl] at Hft; exact Bool.false_ne_true Hft
      obtain ⟨snd', Hpv2, Hid2, Had2⟩ := Hsnd
      iunfold hdrOwn at Hhdr
      icases Hhdr with ⟨%Hpv3, Hi2, Ha2⟩
      iapply wp_fupd
      wp_auto
      wp_apply wp_fromAppendResp $$ [$Hrep $Hi2 $Ha2] as %a2 %b2 ⟨-, -, -, Hi3, Ha3⟩
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
      simp only [github_com.hashicorp.raft.aeResp, github_com.hashicorp.raft.hdrOk]
      rw [HTe, HSu, Hpv3, Hpv2]
      iframe HRt HRs
      iexists snd'
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
