/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__tryStageCommitIndex.lean (241f27e).
-/
/-
`raft.(*Raft).tryStageCommitIndex`'s spec (internal to the RPC handlers): stages the commit index (or nothing).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).tryStageCommitIndex`: stages `c` (a `CommitTrackingLogStore` with
`RestoreCommittedLogs` on) or nothing (hraft_robust: either value of `RestoreCommittedLogs`). (hraft_robust R4a, for
R4b's `dispatchLogs`) With the main goroutine's stable view `stVS rc D g` (its staged commit index
`g`): afterwards the staged index is `c` or unchanged. -/
abbrev github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (c : w64) (D : StableAbs) (g : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ stVS rc D g }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"tryStageCommitIndex")) (Val #c))
  {{ RET #(); ∃ g' : w64, stVS rc D g' ∗ ⌜g' = c ∨ g' = g⌝ }}

end spec

end Perennial
