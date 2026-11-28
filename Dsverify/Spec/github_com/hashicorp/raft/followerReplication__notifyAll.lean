/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/followerReplication__notifyAll.lean (241f27e).
-/
/-
`raft.(*followerReplication).notifyAll`'s spec (replication subsystem, internal).
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

/-- `(*followerReplication).notifyAll(false)` (stage 2, REPL-1; by `handleStaleTerm`): every
registered verify future of the notify set gets a `false` vote (sent back on `verifyCh`, whose bag
`isRaft` gives); the set is emptied. A `true` call would need each future's witness: excluded. -/
abbrev github_com.hashicorp.raft.followerReplication.notifyAll.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ ⌜b = false⌝ }}
    (App (Val (s @!! go.GoType.PointerType followerReplication.ty @!! go!"notifyAll")) (Val #b))
  {{ RET #(); True }}

end spec

end Perennial
