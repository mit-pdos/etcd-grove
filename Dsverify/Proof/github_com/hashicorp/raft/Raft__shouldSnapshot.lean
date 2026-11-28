/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__shouldSnapshot.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).shouldSnapshot`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__shouldSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config

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

theorem github_com.hashicorp.raft.Raft.shouldSnapshot.wp_proof
    (wp_getLastSnapshot : github_com.hashicorp.raft.raftState.getLastSnapshot.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.shouldSnapshot.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
