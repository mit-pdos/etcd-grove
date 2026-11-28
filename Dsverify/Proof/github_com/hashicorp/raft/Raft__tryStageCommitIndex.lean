/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__tryStageCommitIndex.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).tryStageCommitIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryStageCommitIndex
public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash

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

theorem github_com.hashicorp.raft.Raft.tryStageCommitIndex.wp_proof :
    github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG) :=
  fun r γ rc i c D g => by
  wp_start as ⟨#Hr, Hst⟩
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, -, -, -, -, %rcl, #Hrcl⟩
  ihave ⟨%lsx, #Hlsf, #Hls, %HnM⟩ := isRaft_logStore r γ rc i $$ Hr
  ihave #Hdur := isRaft_durInv r γ rc i $$ Hr
  wp_auto
  cases rcl
  · -- `RestoreCommittedLogs` off: nothing
    wp_auto
    iapply HΦ
    iexists g
    iframe
    ipureintro; exact Or.inr rfl
  wp_auto
  unfold isLogStore
  icases Hls with ⟨-, -, -, -, -, -, Hct⟩
  icases Hct with (%hct | ⟨%hct, #HStage, -⟩)
  · -- not a `CommitTrackingLogStore`: nothing
    simp only [hct]
    wp_auto
    iapply HΦ
    iexists g
    iframe
    ipureintro; exact Or.inr rfl
  -- `StageCommitIndex(c)`: the staged index and the main goroutine's view move to `c` together
  simp only [hct]
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HStage
  iintro Hnc
  ihave Hacc := durOpen γ rc i (E := ⊤ \ ↑storeN) (by unfold storeN durN raftN; solve_ndisj) $$ Hdur
  imod Hacc $$ Hnc with ⟨Hnc, %X, Hc, Hs, Hclose⟩
  ihave ⟨Hc, Hst, %Hag⟩ := durCore_stVS_agree γ rc i X D g $$ [$Hc $Hst]
  unfold durCore
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, Hst', Htv, Hcv, %Hp, Hrest⟩
  unfold durStores
  icases Hs with ⟨HownL, Hs⟩
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.A
  iframe HownL
  iintro HownL
  imod Hmask with -
  unfold stVS
  imod ghostVar_update_halves (X.D, c) _ _ _ $$ Hst' Hst with ⟨Hst', Hst⟩
  imod Hclose $$ %{ X with A := { X.A with staged := c } } [H1 H2 H3 H4 H5 H6 Hst' Htv Hcv Hrest] [HownL Hs] with -
  · dsimp only
    iframe
    ipureintro; exact Hp
  · inext
    dsimp only
    iframe
  imodintro
  wp_auto
  iapply HΦ
  iexists c
  rw [← Hag.1]
  iframe
  ipureintro; exact Or.inl rfl

end proof

end Perennial
