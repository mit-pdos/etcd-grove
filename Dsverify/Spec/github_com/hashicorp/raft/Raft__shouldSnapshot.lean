/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__shouldSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).shouldSnapshot`'s spec (raft-internal; stage 3: any answer).
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

/-- `(*Raft).shouldSnapshot()`: whether the log grew by `SnapshotThreshold` since the last snapshot
(stage 3: any answer; the snapshot goroutine's safety does not depend on it). -/
abbrev github_com.hashicorp.raft.Raft.shouldSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"shouldSnapshot")) (Val #()))
  {{ (b : Bool), RET #b; rtok tid }}

end spec

end Perennial
