/-
The proof of `rpctransport.pipeline.run` (ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline__run
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__AppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture__Request
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture__Response
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture__Start

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
/-- A completed future, converted to the `AppendFuture` interface, meets `pipeFut`. -/
theorem pipeFut_intro
    (wp_Request : github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Request.spec (GF := GF) (hG := hG))
    (wp_Response : github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Response.spec (GF := GF) (hG := hG))
    (wp_Start : github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Start.spec (GF := GF) (hG := hG))
    (γ : github_com.hashicorp.raft.gprot.GNames) (j : github_com.hashicorp.raft.proto.SID) (T : Nat) (fl : Loc) (ts : time.Time) (args resp : Loc)
    (rq : github_com.hashicorp.raft.AppendEntriesRequest) (snd : github_com.hashicorp.raft.proto.SID) (prev pt : Nat) (ents : github_com.hashicorp.raft.proto.RLog) (lci : Nat) (ss : github_com.hashicorp.raft.proto.Snap)
    (rp : github_com.hashicorp.raft.AppendEntriesResponse) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
      fl.[appendFuture, go!"start"] ↦□ ts ∗ fl.[appendFuture, go!"req"] ↦□ args ∗
      fl.[appendFuture, go!"resp"] ↦□ resp ∗ args ↦□ rq ∗ github_com.hashicorp.raft.aeReq γ rq snd T prev pt ents lci ss ∗
      resp ↦ rp ∗ github_com.hashicorp.raft.pipeResp γ rp j T (prev + ents.length) (github_com.hashicorp.raft.isHb prev ents lci) ⊢
      github_com.hashicorp.raft.pipeFut γ j T (interface.mkOk (go.GoType.PointerType appendFuture.ty) #fl) := by
  iintro ⟨#Hpkg, #Hstart, #Hreq, #Hresp, #Hargs, #Hrq, Hrp, Hpr⟩
  unfold github_com.hashicorp.raft.pipeFut
  iexists (interface.mk (go.GoType.PointerType appendFuture.ty) #fl), args, resp, rq, snd, prev, pt,
    ents, lci, ss, rp
  iframe Hargs Hrq Hrp Hpr
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %Φ HΦ
    iapply wp_Request fl args $$ [$Hpkg $Hreq]
    inext; iintro -; iexact HΦ
  isplitr
  · imodintro
    iintro %Φ HΦ
    iapply wp_Response fl resp $$ [$Hpkg $Hresp]
    inext; iintro -; iexact HΦ
  · imodintro
    iintro %Φ HΦ
    iapply wp_Start fl ts $$ [$Hpkg $Hstart]
    inext; iintro -; iapply HΦ

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.run.wp_proof
    (wp_AE : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.AppendEntries.spec (GF := GF) (hG := hG))
    (wp_Request : github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Request.spec (GF := GF) (hG := hG))
    (wp_Response : github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Response.spec (GF := GF) (hG := hG))
    (wp_Start : github_com.hashicorp.raft.examples.hraftnet.rpctransport.appendFuture.Start.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.run.spec (GF := GF) (hG := hG) := by
  intro p γ j T
  wp_start as #Hp
  iNamed Hp
  wp_auto_lc 2
  wp_for
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  rotate_left
  · -- the pipeline is closed
    iapply BigAndL.bigAndL_singleton.2
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, cc, γcl
    isplitr; · ipureintro; rfl
    isplitr; · iapply ownBroadcastChan_is_chan $$ Hclose
    iapply broadcast_chan_receive $$ Hclose
    iintro -
    wp_auto
    wp_for_post
    iapply HΦ; itrivial
  simp only [chan.blockingClausePre]
  iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, q, γq
  isplitr; · ipureintro; rfl
  isplitr; · iapply is_bag_is_chan $$ Hqb
  iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqb
  inext
  iintro %fl Hf
  iNamed Hf
  wp_auto
  wp_apply (lc := 4) (wp_AE t γ snapP i W C go!"" j args resp rq rp0 DfracDiscarded snd T prev pt ents lci ss)
    $$ [$Htr $Hargs $Hrq $Hrp] as %err ⟨-, Hres⟩
  ihave Hdone : (∃ rp : github_com.hashicorp.raft.AppendEntriesResponse, resp ↦ rp ∗
      github_com.hashicorp.raft.pipeResp γ rp j T (prev + ents.length) (github_com.hashicorp.raft.isHb prev ents lci)) ∗
      (⌜err = interface.nil⌝ ∨ github_com.hashicorp.raft.errOk err) $$ [Hres]
  · icases Hres with (⟨%Herr, %rp, Hrp, Hae⟩ | ⟨#He, Hrp⟩)
    · isplitl [Hrp Hae]
      · iexists rp
        iframe Hrp
        unfold github_com.hashicorp.raft.aeResp github_com.hashicorp.raft.pipeResp
        icases Hae with ⟨-, Hs, -⟩
        icases Hs with (%Hf | ⟨Hh, -⟩)
        · ileft; ipureintro; exact Hf
        · iright; iexact Hh
      · ileft; ipureintro; exact Herr
    · isplitl [Hrp]
      · iexists rp0
        iframe Hrp
        unfold github_com.hashicorp.raft.pipeResp
        ileft; ipureintro; exact Hrp0
      · iright; iapply errStr_errOk $$ He
  icases Hdone with ⟨⟨%rp, Hrp, Hpr⟩, #He⟩
  (try wp_auto)
  ipersist Herr
  ihave #HQd : futErrDone fl $$ []
  · unfold futErrDone; iexists err; iframe #
  wp_apply wp_broadcast_chan_close $$ [$Hdc $HQd] as -
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  rotate_left
  · -- the pipeline is closed
    iapply BigAndL.bigAndL_singleton.2
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, cc, γcl
    isplitr; · ipureintro; rfl
    isplitr; · iapply ownBroadcastChan_is_chan $$ Hclose
    iapply broadcast_chan_receive $$ Hclose
    iintro -
    wp_auto
    wp_for_post
    iapply HΦ; itrivial
  -- the future, completed, to the consumer
  ihave Hfut := pipeFut_intro wp_Request wp_Response wp_Start γ j T fl ts args resp rq snd
    prev pt ents lci ss rp $$ [$Hpkg $Hstart $Hreq $Hresp $Hargs $Hrq $Hrp $Hpr]
  simp only [chan.blockingClausePre]
  iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, cons, γc,
    (interface.mkOk (go.GoType.PointerType appendFuture.ty) #fl)
  isplitr; · ipureintro; exact ⟨rfl, rfl⟩
  isplitr; · iapply is_bag_is_chan $$ Hcb
  iapply bag_send_au $$ [$Hlc1 $Hlc2] Hcb Hfut
  inext
  wp_auto
  wp_for_post
  iframe


end proof

end Perennial
