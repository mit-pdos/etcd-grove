/-
Package `proxy`: `Proxy.Run` (`proxy.go`): the main loop's goroutine (a blocking select over its
six input channels, each case a handler over the main loop's state `ownQ`) and the batch
timer's goroutine; from the handlers' specs.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

instance rlp_notInterface_int64 : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩

/-- The `proposeRequestIndex` channel of the main loop's state (persistent). -/
theorem ownQ_reqChan (γ : QNames) (cf : QConf) (k : Nat) (pr : Loc) (γq : GName) :
    ⊢@{IProp GF} ownQ γ cf k pr γq -∗ ownQ γ cf k pr γq ∗
      chanField ProposeRequestIndex.ty pr go!"proposeRequestIndex" (reqIdxP γq) := by
  iintro Hown
  iunfold ownQ at Hown
  icases Hown with ⟨%γs, %cb, %bm, %ebm, %rl, %slots, %L, %c, %lp, %D, %Bm, %tb, %tbs, H1, H2, H3,
    H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Hepo, Hprop⟩
  iunfold ownProp at Hprop
  icases Hprop with ⟨%Pm, %its, %ts, %tlp, %bt, ⟨%_hs, #Hch⟩, P2, P3, P4, P5, P6, P7, P8, P9⟩
  isplitl
  · iunfold ownQ
    iexists γs, cb, bm, ebm, rl, slots, L, c, lp, D, Bm, tb, tbs
    iframe
    iunfold ownProp
    iexists Pm, its, ts, tlp, bt
    iframe
    iexists _hs
    iexact Hch
  · iexact Hch

theorem wp_Run
    (wp_hcb : handleClientBatch_spec (GF := GF) (hG := hG))
    (wp_pti : proposeToIndex_spec (GF := GF) (hG := hG))
    (wp_hpr : handleProposeResponse_spec (GF := GF) (hG := hG))
    (wp_hrr : handleRecorderResponse_spec (GF := GF) (hG := hG))
    (wp_hfr : handleFetchResponse_spec (GF := GF) (hG := hG)) :
    Proxy.Run.spec (GF := GF) (hG := hG) := by
  intro γ cf k pr
  wp_start as ⟨Hown, #Hsh⟩
  unfold proxyOwn proxyShared at *
  iunfold proxyOwnDef at Hown
  icases Hown with ⟨%γq, Hown⟩
  icases ownQ_reqChan γ cf k pr γq $$ Hown with ⟨Hown, #Hreq⟩
  ihave #Hsh' := Hsh
  iunfold proxySharedDef at Hsh'
  icases Hsh' with ⟨%_hs, %_γs', %_cb', %_bm', %_ebm', #Hfacts, #Hconsts, -, #Hchans, #Hloop, -⟩
  iunfold sharedChans at Hchans
  icases Hchans with ⟨-, -, -, #Hrec, -⟩
  iunfold sharedLoop at Hloop
  icases Hloop with ⟨%_hs2, #Hinc, #Hcbt, #Hcrq, #Hppc, #Hpfc, %rpt, #Hrpt⟩
  iunfold chanField at Hreq Hrec Hinc Hcbt Hcrq Hppc Hpfc
  icases Hreq with ⟨%ch0, %γ0, #Hch0, #Hbag0⟩
  icases Hppc with ⟨%ch1, %γ1, #Hch1, #Hbag1⟩
  icases Hrec with ⟨%ch2, %γ2, #Hch2, #Hbag2⟩
  icases Hpfc with ⟨%ch3, %γ3, #Hch3, #Hbag3⟩
  icases Hcrq with ⟨%ch4, %γ4, #Hch4, #Hbag4⟩
  icases Hinc with ⟨%ch5, %γ5, #Hch5, #Hbag5⟩
  icases Hcbt with ⟨%ch6, %γ6, #Hch6, #Hbag6⟩
  wp_auto
  ipersist pr
  wp_apply wp_fork $$ [Hown]
  · ihave HI : ("Hown" ∷ ownQ γ cf k pr γq : IProp GF) $$ [Hown]
    · iframe
    wp_call
    wp_for_core
    iNamed HI
    wp_pure_lc Hlc1
    iapply wp_value'
    simp only [decide_true, ↓reduceIte]
    wp_pure_lc Hlc2
    wp_auto
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists ProposeRequestIndex, inferInstance, inferInstance, inferInstance, inferInstance, ch0, γ0
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag0
      iapply bag_recv_au γ0 ch0 _ _ $$ [$Hlc1 $Hlc2] Hbag0
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_pti $$ [Hown Hv] as Hown
      · iframe Hsh Hown; iexact Hv
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists ProposeResponse, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag1
      iapply bag_recv_au γ1 ch1 _ _ $$ [$Hlc1 $Hlc2] Hbag1
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_hpr $$ [Hown Hv] as Hown
      · iframe Hsh Hown; iexact Hv
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Decision, inferInstance, inferInstance, inferInstance, inferInstance, ch2, γ2
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag2
      iapply bag_recv_au γ2 ch2 _ _ $$ [$Hlc1 $Hlc2] Hbag2
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_hrr $$ [Hown Hv] as Hown
      · iframe Hsh Hown; iexact Hv
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists FetchResposne, inferInstance, inferInstance, inferInstance, inferInstance, ch3, γ3
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag3
      iapply bag_recv_au γ3 ch3 _ _ $$ [$Hlc1 $Hlc2] Hbag3
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_hfr $$ [Hown Hv] as Hown
      · iframe Hsh Hown; iexact Hv
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raxos.proto.client.ClientBatch, inferInstance, inferInstance, inferInstance, inferInstance, ch4, γ4
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag4
      iapply bag_recv_au γ4 ch4 _ _ $$ [$Hlc1 $Hlc2] Hbag4
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_hcb $$ [Hown Hv] as Hown
      · iframe Hsh Hown; iexact Hv
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raxos.common.RPCPair, inferInstance, inferInstance, inferInstance, inferInstance, ch5, γ5
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hbag5
      iapply bag_recv_au γ5 ch5 _ _ $$ [$Hlc1 $Hlc2] Hbag5
      inext
      iintro %v Hv
      iunfold incomingP at Hv
      icases Hv with ⟨%l, %b, %t, %Hpure, Hcb, #Hreg, Hcr⟩
      obtain ⟨Hcode, Hobj, Hbok⟩ := Hpure
      iunfold repCB at Hcb
      icases Hcb with ⟨%x, #Hl, #Hrep⟩
      ihave #Hconsts' := Hconsts
      iunfold sharedConsts at Hconsts'
      icases Hconsts' with ⟨-, #Hrpc, -⟩
      wp_auto
      rw [Hcode]
      wp_auto
      rw [Hobj]
      simp only [interface.mkOk, ↓reduceIte]
      wp_auto
      wp_apply wp_time_Now as %tm -
      wp_apply wp_bag_send $$ [Hcr]
      · iframe Hbag6
        dsimp only
        iunfold cbReqP
        iexists b, t
        iframe Hrep Hreg Hcr
        ipureintro; exact Hbok
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_nil.2
    itrivial
  wp_apply wp_fork $$ []
  · wp_call
    wp_for
    wp_apply (wp_bag_receive γ6 ch6) $$ [Hbag6] as %bt Hbt
    · iexact Hbag6
    wp_apply wp_time_Now as %tm -
    wp_apply time.Time.wp_Sub as %d -
    wp_apply (time.Duration.wp_Milliseconds d)
    wp_if_destruct
    · wp_apply wp_bag_send $$ [Hbt]
      · iframe Hbag4; iexact Hbt
      wp_for_post
      iexact __CTX
    · wp_apply wp_bag_send $$ [Hbt]
      · iframe Hbag6; iexact Hbt
      wp_for_post
      iexact __CTX
  wp_end

end proofs

end Perennial.raxos
