/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__setState.lean (241f27e).
-/
/-
`raft.(*raftState).setState`'s spec (raft-internal interface, notes/raft-iface.md). The raw atomic store, called as `r.raftState.setState(s)` by `(*Raft).setState` (the receiver is the embedded `raftState`); the main goroutine owns the other half of the ghost variable.
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

/-- `(*raftState).setState`: The raw atomic store, called as `r.raftState.setState(s)` by `(*Raft).setState` (the receiver is the embedded `raftState`); the main goroutine owns the other half of the ghost variable. -/
abbrev github_com.hashicorp.raft.raftState.setState.spec : Prop :=
  ∀ (r : Loc) (rc : RCtx GF) (st0 st : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ stateCell r rc ∗ ghostVar rc.names.state (1 : Qp).half st0 ∗
     ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝ }}
    (App (Val ((r.[Raft, go!"raftState"]) @!! go.GoType.PointerType raftState.ty @!! go!"setState")) (Val #st))
  {{ RET #(); ghostVar rc.names.state (1 : Qp).half st }}

end spec

end Perennial
