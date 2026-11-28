/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__setLastLog.lean (241f27e).
-/
/-
`raft.(*raftState).setLastLog`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted), by the main goroutine.
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

/-- `(*raftState).setLastLog`: Called through `*Raft` (promoted), by the main goroutine.
(hraft_robust R4a, after R5's `lastLockInv` fix: its ghost is the effective last entry, the later of
the last log entry and the last snapshot) The new last index is at least the main goroutine's
`lastApplied` `a` (its authority half), which bounds the last snapshot's index (`applLb`): so the new
entry is the effective one. -/
abbrev github_com.hashicorp.raft.raftState.setLastLog.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (p : Nat × Nat) (a : Nat) (x y : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ghostVar rc.names.lastLog (1 : Qp).half p ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
     ⌜a ≤ uint.nat x⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastLog")) (Val #x)) (Val #y))
  {{ RET #(); ghostVar rc.names.lastLog (1 : Qp).half (uint.nat x, uint.nat y) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a }}

end spec

end Perennial
