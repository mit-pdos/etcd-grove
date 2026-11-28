/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__goFunc.lean (241f27e).
-/
/-
`raft.(*raftState).goFunc`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). Starts `f` in a goroutine (counted by `routinesGroup`): the caller keeps its thread token; `f` runs with a thread token and ends with one, without panicking.
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

/-- `(*raftState).goFunc`: Called through `*Raft` (promoted). Starts `f` in a goroutine (counted by `routinesGroup`): the caller keeps its thread token; `f` runs with a thread token and ends with one, without panicking. -/
abbrev github_com.hashicorp.raft.raftState.goFunc.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (f : GoFunc) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rtok tid ∗
     (∀ tid' : Nat, rtok tid' -∗ WP (App (Val #f) (Val #())) {{ fun v => iprop(⌜v = #()⌝ ∗ rtok tid') }}) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"goFunc")) (Val #f))
  {{ RET #(); rtok tid }}

end spec

end Perennial
