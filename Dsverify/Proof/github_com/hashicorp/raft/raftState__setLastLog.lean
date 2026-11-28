/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__setLastLog.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).setLastLog` (called through `*Raft`): writes under `lastLock`,
updating both halves of its ghost variable.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
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

theorem github_com.hashicorp.raft.raftState.setLastLog.wp_proof :
    github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
