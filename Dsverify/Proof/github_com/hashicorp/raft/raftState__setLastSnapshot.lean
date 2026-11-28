/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__setLastSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).setLastSnapshot` (called through `*Raft`): writes the last
snapshot under `lastLock`, with `lastLockInv`'s facts for it.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastSnapshot
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers

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

theorem github_com.hashicorp.raft.raftState.setLastSnapshot.wp_proof :
    github_com.hashicorp.raft.raftState.setLastSnapshot.spec (GF := GF) (hG := hG) := by
  intro r γ rc i si st
  wp_start as ⟨#His, #Hnew⟩
  ihave #Hm := isRaft_lastLock r γ rc i $$ His
  ihave #Hcl := isRaft_cells r γ rc i $$ His
  unfold raftCells
  icases Hcl with ⟨-, -, -, -, -, -, -, #Hnone⟩
  wp_method_call; wp_call
  wp_auto
  wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hm] with ⟨Hown, HL⟩
  iunfold lastLockInv at HL
  icases HL with ⟨%x0, %y0, %si0, %st0, Hx, Hy, Hsi, Hst, Hg', -, -⟩
  wp_auto
  wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg']
  · iframe #; iframe; inext; iunfold lastLockInv; iexists x0, y0, si, st
    iframe Hx Hy Hsi Hst Hg'
    isplitr
    · iexact Hnew
    · ileft; iexact Hnone
  iapply HΦ; itrivial

end proof

end Perennial
