/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getState.lean (241f27e).
-/
/-
`raft.(*raftState).getState`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). Strong form: with the main goroutine's half of the `state` ghost variable, the exact value; weak form: one of the three states.
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

/-- `(*raftState).getState`: Called through `*Raft` (promoted). Strong form: with the main goroutine's half of the `state` ghost variable, the exact value; weak form: one of the three states. -/
abbrev github_com.hashicorp.raft.raftState.getState.spec : Prop :=
  (∀ (r : Loc) (rc : RCtx GF) (st : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ stateCell r rc ∗ ghostVar rc.names.state (1 : Qp).half st }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getState")) (Val #()))
  {{ RET #st; ghostVar rc.names.state (1 : Qp).half st }}) ∧
  (∀ (r : Loc) (rc : RCtx GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ stateCell r rc }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getState")) (Val #()))
  {{ (st : w32), RET #st; ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝ }})

end spec

end Perennial
