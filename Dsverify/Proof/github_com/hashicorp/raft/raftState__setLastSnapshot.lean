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
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
