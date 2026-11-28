/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__restoreFromCommittedLogs.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).restoreFromCommittedLogs` (hraft_robust rcl: either value of `RestoreCommittedLogs`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__restoreFromCommittedLogs
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processLogs
public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftRcl

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.wp_proof
    (wp_setCommitIndex : github_com.hashicorp.raft.raftState.setCommitIndex.spec (GF := GF) (hG := hG))
    (wp_processLogs : github_com.hashicorp.raft.Raft.processLogs.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.spec (GF := GF) (hG := hG) := by
  intro r γ rc i b x s a c tid
  wp_start as ⟨#Hr, #Hrcl, #Hlogs, %Hct, Hsv, Hprod, Happ, Hcomp, %Hca, Htok⟩
  wp_auto
  cases b
  · -- `RestoreCommittedLogs` off: nothing
    wp_auto
    iapply HΦ
    iexists s.cidx
    have hmax : Max.max a s.cidx = a := Nat.max_eq_left Hca.2
    rw [hmax]
    iframe
    ipureintro; exact Or.inl ⟨rfl, rfl⟩
  rcases Hct with h | hct
  · cases h
  ihave ⟨%lsx, #Hlsf, #Hls, -⟩ := isRaftCore_logStore r γ rc i $$ Hr
  icombine Hlsf Hlogs gives %hx
  cases hx
  ihave #Hcells := isRaftCore_cells r γ rc i $$ Hr
  unfold raftCellsCore
  icases Hcells with ⟨-, #HcidxC, #Hdur, -⟩
  ihave ⟨#Hinv, -⟩ := isRaftCore_proto r γ rc i $$ Hr
  unfold isLogStore
  icases Hls with ⟨#HLI, -, -, -, -, -, Hct'⟩
  icases Hct' with (%hn | ⟨-, -, #HGCI⟩)
  · rw [hct] at hn; cases hn
  wp_auto
  simp only [hct]
  wp_auto
  -- `GetCommitIndex()`: the written commit index (capped at `hi`), durable
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HGCI $$ Htok
  iapply (mainRead_L γ rc i s)
  iframe Hdur Hsv
  iintro Hsv %A %hA Htok
  have hci : uint.nat A.readCi ≤ s.dur.1 := by
    unfold LogAbs.readCi; split <;> omega
  wp_auto
  -- `LastIndex()`
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HLI $$ Htok
  iapply (mainRead_L γ rc i s)
  iframe Hdur Hsv
  iintro Hsv %A2 %- Htok
  wp_auto
  -- `commitIndex = min(commitIndex, lastIndex)`: still durable
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ k : w64, commitIndex_ptr ↦ k ∗ ⌜uint.nat k ≤ s.dur.1⌝))) $$ [commitIndex lastIndex] [-]
  · wp_if_destruct
    · isplitr; · ipureintro; trivial
      iexists _; iframe; ipureintro; word
    · isplitr; · ipureintro; trivial
      iexists _; iframe; ipureintro; exact hci
  iintro %v ⟨%hv, %k, commitIndex, %hk⟩
  subst hv
  wp_auto
  -- `setCommitIndex(k)`: the main goroutine's commit index (`setCidx_R`)
  wp_apply (wp_setCommitIndex r γ rc i k iprop(srvV rc { s with cidx := uint.nat k })) $$ [Hsv]
  · iframe #
    iintro %c0 Hcv Hnc
    ihave H := setCidx_R γ rc i gd_diff_cidxN s (uint.nat k) c0 hk $$ [$Hinv $Hdur $Hsv $Hcv]
    imod H $$ Hnc with ⟨Hnc, Hsv, Hcv⟩
    imodintro; iframe
  iintro Hsv
  wp_auto
  -- `processLogs(k, nil)`: the entries up to `k` applied
  wp_apply wp_processLogs r γ rc i k _ ∅ { s with cidx := uint.nat k } a c tid
    $$ [$Hr $Hsv $Hprod $Happ $Hcomp $Htok] as ⟨Hsv, Hprod, Happ, Hcomp, Htok, -⟩
  · isplitr; · ipureintro; exact hk
    isplitr; · ipureintro; exact Hca.1
    isplitr; · ileft; ipureintro; exact ⟨rfl, rfl⟩
    iapply BigSepM.bigSepM_empty.2; iempintro
  iapply HΦ
  iexists (uint.nat k)
  iframe
  ipureintro; exact Or.inr ⟨trivial, hk⟩

end proof

end Perennial
