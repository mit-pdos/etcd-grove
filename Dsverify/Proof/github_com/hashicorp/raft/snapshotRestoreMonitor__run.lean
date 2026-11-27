/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/snapshotRestoreMonitor__run.lean (241f27e).
-/
/-
The proof of `raft.snapshotRestoreMonitor__run` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__run
public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__runOnce
public import Perennial.Proof.time.Link
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.snapshotRestoreMonitor.run.wp_proof
    (wp_Stop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (wp_runOnce : github_com.hashicorp.raft.snapshotRestoreMonitor.runOnce.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.snapshotRestoreMonitor.run.spec (GF := GF) (hG := hG) := by
  intro m ctx desc dch γd
  wp_start as ⟨#Hd, Hbc, #Hctx⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply time.wp_NewTicker as %tk %tch %γt #Htk
  · ipureintro; decide
  try wp_auto
  ihave #Htk' := Htk
  unfold time.isTicker
  icases Htk' with ⟨#HC, -, -, #Htbag⟩
  ihave #HDn := context.isContext_Done ctx desc $$ Hctx
  ihave HI : (∃ b : Bool, "ranOnce" ∷ ranOnce_ptr ↦ b : IProp GF) $$ [ranOnce]
  · iexists _; iexact ranOnce
  wp_for HI
  wp_apply (lc := 2) HDn as %dch2 %γch #Hdone
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the context is done: stop
    dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch2, γch
    isplitr
    · ipureintro; rfl
    ihave #Hdc := context.isContextDone_is_chan _ _ _ $$ Hdone
    iframe Hdc
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    cases b
    · wp_auto
      wp_apply wp_runOnce
      wp_for_post
      wp_apply wp_Stop $$ []
      · iexists _, _; unfold time.isTicker; iexact Htk
      try wp_auto
      wp_apply (wp_broadcast_chan_close (ty := go.ChannelType go.sendrecv (go.StructType [])) dch γd
        iprop(True)) $$ [$Hbc] as -
      · iintro !>; itrivial
      try wp_auto
      iapply HΦ; itrivial
    · wp_auto
      wp_for_post
      wp_apply wp_Stop $$ []
      · iexists _, _; unfold time.isTicker; iexact Htk
      try wp_auto
      wp_apply (wp_broadcast_chan_close (ty := go.ChannelType go.sendrecv (go.StructType [])) dch γd
        iprop(True)) $$ [$Hbc] as -
      · iintro !>; itrivial
      try wp_auto
      iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick
    dsimp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    ihave #Htc := is_bag_is_chan _ _ _ $$ Htbag
    iframe Htc
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %v -
    wp_auto
    wp_apply wp_runOnce
    wp_for_post
    iframe
    iexists _; iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial
