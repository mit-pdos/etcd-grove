/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/startSnapshotRestoreMonitor.lean (241f27e).
-/
/-
The proof of `raft.startSnapshotRestoreMonitor` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.startSnapshotRestoreMonitor
public import Dsverify.Spec.github_com.hashicorp.raft.snapshotRestoreMonitor__run
public import Perennial.Proof.context.Results
public import Perennial.Proof.sync.Results

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

theorem github_com.hashicorp.raft.startSnapshotRestoreMonitor.wp_proof
    (wp_run : github_com.hashicorp.raft.snapshotRestoreMonitor.run.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.startSnapshotRestoreMonitor.spec (GF := GF) (hG := hG) := by
  intro cr size nt
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply context.wp_Background
  ihave #Hctxi : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcl := context.isClosedchanInit_of_init $$ Hctxi
  wp_apply (context.wp_WithCancel_Background (iprop(True))) $$ [$Hcl] as %ctx %γc %cancel ⟨#Hcancel, #Hctx, -⟩
  wp_apply (chan.wp_make1 (V := Unit)) as %dch %γd ⟨#Hisch, %Hcap, Hoc⟩
  imod alloc_broadcast_chan (iprop(True)) γd dch $$ Hisch Hoc with Hbc
  try wp_auto
  irename «$r0» => Hm
  generalize «$r0_ptr» = mm at *
  iStructNamed Hm
  ipersist cancel
  ipersist doneCh
  imod sync.init_Once _ (iprop(True)) (iprop(True)) ⊤ $$ [once] with #Honce
  · iframe
  ihave #HbcU := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
  wp_bind
  iapply wp_fork $$ [Hbc]
  · inext
    wp_apply wp_run mm ctx _ dch γd $$ [$doneCh $Hbc $Hctx]
    ipureintro; exact isPanic_intoVal ()
  inext
  wp_auto
  imodintro
  iapply HΦ
  unfold monitorOwn
  iexists cancel, dch, γd
  iframe #
  iintro !> %Φ' HΦ'
  iapply Hcancel $$ %Φ' []
  · iintro !>; itrivial
  inext; iintro -; iexact HΦ'

end proof

end Perennial
