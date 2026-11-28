/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getLastLog.lean (241f27e).
-/
/-
`raft.(*raftState).getLastLog`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted). Strong form: the main goroutine (holding the other half of `lastLog`) reads the exact values; weak form: any goroutine reads some values.
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

/-- `(*raftState).getLastLog`: Called through `*Raft` (promoted). Strong form: the main goroutine (holding the other half of `lastLog`) reads the exact values; weak form: any goroutine reads some values. -/
/- (hraft_robust R4a) Strong form: the raw last log entry, at most the effective one (`lastLockInv`'s
ghost, the later of the last log entry and the last snapshot; was: equal to it, false after R5's fix). -/
abbrev github_com.hashicorp.raft.raftState.getLastLog.spec : Prop :=
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (li lt : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ ghostVar rc.names.lastLog (1 : Qp).half (li, lt) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastLog")) (Val #()))
  {{ (x y : w64), RET (PairV #x #y); ⌜uint.nat x ≤ li ∧ (uint.nat x = li → uint.nat y = lt)⌝ ∗
      ghostVar rc.names.lastLog (1 : Qp).half (li, lt) }}) ∧
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastLog")) (Val #()))
  {{ (x y : w64), RET (PairV #x #y); True }})

end spec

end Perennial
