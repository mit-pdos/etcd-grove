/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__setLastSnapshot.lean (241f27e).
-/
/-
`raft.(*raftState).setLastSnapshot`'s spec (stage 3, raft-internal: the snapshot goroutine's `takeSnapshot` and the main goroutine's `installSnapshot`).
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

/-- `(*raftState).setLastSnapshot(si, st)`: Called through `*Raft` (promoted). Stores the last
snapshot under `lastLock`, given `lastLockInv`'s facts for it: none, or a committed entry of term `st`
at `si`, at most `lastApplied` (`applLb`), durable at `i` (`takeSnapshot`, from the configurations
answer) or installed while `i` followed (`installSnapshot`, after its `setLastApplied`). -/
abbrev github_com.hashicorp.raft.raftState.setLastSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (si st : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     (⌜si = W64 0⌝ ∨ ∃ e : Entry, CIdx γ (uint.nat si) e ∗ ⌜e.term = uint.nat st⌝ ∗
       applLb rc (uint.nat si) ∗
       (durLb γ i (uint.nat si) ∨ snapFollow γ i (uint.nat si) (uint.nat st))) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastSnapshot")) (Val #si)) (Val #st))
  {{ RET #(); True }}

end spec

end Perennial
