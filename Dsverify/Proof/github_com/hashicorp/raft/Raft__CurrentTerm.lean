/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__CurrentTerm.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).CurrentTerm`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__CurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap

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

/-- The term cell gives the (trivial) lower bound `0` on the term. -/
theorem github_com.hashicorp.raft.termCell_lb0 (r : Loc) (γ : gprot.GNames) (i : SID) :
    £ 1 ∗ termCell (GF := GF) r γ i ⊢ |={⊤}=> gprot.termLb γ i 0 := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

theorem github_com.hashicorp.raft.Raft.CurrentTerm.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.CurrentTerm.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
