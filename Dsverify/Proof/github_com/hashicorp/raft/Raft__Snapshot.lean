/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__Snapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).Snapshot` (stage 3, the user snapshot API).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__Snapshot
public import Dsverify.Proof.github_com.hashicorp.raft.SnapFut

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

theorem github_com.hashicorp.raft.Raft.Snapshot.wp_proof :
    github_com.hashicorp.raft.Raft.Snapshot.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #Hr
  wp_auto
  ihave Hch := isRaft_chans r γ rc i $$ Hr
  unfold raftChans deadField deadChan
  icases Hch with ⟨-, -, -, -, -, -, ⟨%uch, #Huch, %γu, #Hbag⟩, -, -, ⟨%sdCh, #HsdCh, %γsd, #Hsd⟩, -⟩
  irename «$r0» => Hf
  generalize «$r0_ptr» = f at *
  iStructNamed Hf
  try simp only [zeroValDef] at *
  iStructNamed deferError
  wp_apply (lc := 2) snapFut.wp_uf_init f (fun _ => iprop(True)) null $$ [$errCh]
    as ⟨%ch, %γe, %Hne, HerrCh, #Hspsc, Hprod, Hcons⟩
  ipersist HerrCh
  ipersist ShutdownCh
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the send on userSnapshotCh
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, uch, γu, f
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbag [opener responded Hprod]
    · unfold userSnapP
      isplitl [opener]
      · iexists _; iexact opener
      unfold deferResp
      iexists ch
      iframe #
      iright
      iframe
      iframe #
      ipureintro; exact Hne
    inext
    wp_auto
    iapply HΦ
    unfold futWait
    iright; iright; iright; iright; ileft
    iexists f
    isplitr
    · ipureintro; rfl
    unfold deferWait
    iexists ch, γe
    iframe
    iframe #
    isplitr
    · ipureintro; exact Hne
    ileft; ipureintro; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- shutdownCh: never closed, never sent on
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sdCh, γsd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hsd
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsd
    inext
    iintro %t Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial
