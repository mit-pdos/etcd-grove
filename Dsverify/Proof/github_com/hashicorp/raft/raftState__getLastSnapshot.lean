/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__getLastSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).getLastSnapshot` (called through `*Raft`): reads under
`lastLock` (no snapshot: `0, 0`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastSnapshot
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

theorem github_com.hashicorp.raft.raftState.getLastSnapshot.wp_proof :
    github_com.hashicorp.raft.raftState.getLastSnapshot.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #His
  ihave #Hm := isRaft_lastLock r γ rc i $$ His
  wp_method_call; wp_call
  wp_auto
  wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hm] with ⟨Hown, HL⟩
  iunfold lastLockInv at HL
  icases HL with ⟨%x, %y, %si, %st, Hx, Hy, Hsi, Hst, Hg', #Hsnap⟩
  wp_auto
  wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg']
  · iframe #; iframe; inext; iunfold lastLockInv; iexists x, y, si, st; iframe; iframe #
  iapply HΦ
  itrivial

end proof

end Perennial
