/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__handleStaleTerm.lean (241f27e).
-/
/-
`raft.(*Raft).handleStaleTerm`'s spec (replication subsystem, internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

/-- `(*Raft).handleStaleTerm`: vote `false` for the follower's pending verify futures (`notifyAll`,
stage 2: `isRaft` for `verifyCh`, REPL-2) and notify the main goroutine on `stepDown`. -/
abbrev github_com.hashicorp.raft.Raft.handleStaleTerm.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"handleStaleTerm")) (Val #s))
  {{ RET #(); True }}

end spec

end Perennial
