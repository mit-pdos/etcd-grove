/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/NewObserver.lean (241f27e).
-/
/-
The proof of `raft.NewObserver` (with no channel, not blocking): a fresh `Observer` whose
`channel`, `blocking`, `filter` and `id` fields are made read-only; the id comes from
`nextObserverID`'s atomic counter (its invariant is in `isPkgInit`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.NewObserver
public import Perennial.Proof.sync.atomic.Link

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

theorem github_com.hashicorp.raft.NewObserver.wp_proof :
    github_com.hashicorp.raft.NewObserver.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
