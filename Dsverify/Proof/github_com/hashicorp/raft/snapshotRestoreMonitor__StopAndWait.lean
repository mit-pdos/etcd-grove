/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/snapshotRestoreMonitor__StopAndWait.lean (241f27e).
-/
/-
The proof of `raft.(*snapshotRestoreMonitor).StopAndWait` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__StopAndWait
public import Perennial.Proof.sync.Link

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

theorem github_com.hashicorp.raft.snapshotRestoreMonitor.StopAndWait.wp_proof :
    github_com.hashicorp.raft.snapshotRestoreMonitor.StopAndWait.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start as #Hmon
  unfold monitorOwn
  icases Hmon with ⟨%cancel, %dch, %γd, #Hc, #Hd, #Honce, #Hcancel, #Hbc⟩
  wp_auto
  ipersist m
  ihave #Hisd := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
  wp_apply (sync.Once.wp_Do _ iprop(True) iprop(True) _) $$ [$Honce]
  · iintro !> %Ψ - HΨ
    try wp_auto
    wp_apply Hcancel
    try wp_auto
    wp_apply (chan.wp_receive (V := Unit) dch γd) $$ [$Hisd]
    iintro ⟨Hl1, Hl2, Hl3, Hl4⟩
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
    iintro -
    try wp_auto
    iapply HΨ; itrivial
  iapply HΦ; itrivial

end proof

end Perennial
