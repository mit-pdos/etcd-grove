/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__configurationChangeChIfStable.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).configurationChangeChIfStable`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__configurationChangeChIfStable
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Proof.github_com.hashicorp.raft.leader.MainCfg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `configurationChangeChIfStable` reads `commitment.startIndex` without the commitment's lock:
`isCommitment` gives it read-only (MAIN-L 2), (review T1-2) with its value `len0 + 1`. -/
theorem commitment_startIndex (γ : GNames) (i : SID) (T : Nat) (cm : Loc) :
    isCommitment γ i T cm ⊢ (∃ (si : w64) (n0 : Nat), cm.[commitment, go!"startIndex"] ↦□ si ∗
      len0Is γ T n0 ∗ ⌜uint.nat si = n0 + 1⌝ : IProp GF) := by
  unfold isCommitment
  iintro ⟨H, -⟩
  iexact H

end defs
end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

/-- (hub L1) When the channel is returned, the latest configuration is the committed one
(`mainOwnAtSt`), what `appendConfigurationEntry` needs. -/
theorem github_com.hashicorp.raft.Raft.configurationChangeChIfStable.wp_proof
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.configurationChangeChIfStable.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
