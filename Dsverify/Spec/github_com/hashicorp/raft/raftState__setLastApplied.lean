/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__setLastApplied.lean (241f27e).
-/
/-
`raft.(*raftState).setLastApplied`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted), by the main goroutine.
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

/-- `(*raftState).setLastApplied(x)`: Called through `*Raft` (promoted), by the main goroutine.
(Stage 3, check N3) Logically atomic in the holder's half of `lastApplied`'s authority (a
`mono_nat`, `x` not below it), committed at the atomic store: `processLogs` passes its own half; the
install's update opens `snapCell`, takes the half lent there and ends the pending record. -/
abbrev github_com.hashicorp.raft.raftState.setLastApplied.spec : Prop :=
  ∀ (r : Loc) (rc : RCtx GF) (x : w64),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ appliedCell r rc) -∗
    (|={⊤ ∖ ↑appliedN, ∅}=> ▷ ∃ a : Nat, monoNatAuthOwn rc.names.applied (1 : Qp).half a ∗
      ⌜a ≤ uint.nat x⌝ ∗
      (monoNatAuthOwn rc.names.applied (1 : Qp).half (uint.nat x) ={∅, ⊤ ∖ ↑appliedN}=∗ Φ #())) -∗
    WP (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastApplied")) (Val #x)) {{ Φ }}

end spec

end Perennial
