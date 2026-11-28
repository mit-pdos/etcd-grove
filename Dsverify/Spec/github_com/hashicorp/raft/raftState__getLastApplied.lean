/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/raftState__getLastApplied.lean (241f27e).
-/
/-
`raft.(*raftState).getLastApplied`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*Raft` (promoted), by the main goroutine (which holds the other half).
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

/-- `(*raftState).getLastApplied`: Called through `*Raft` (promoted), by the main goroutine (which holds
the other half of the authority; stage 3: a `mono_nat`). -/
abbrev github_com.hashicorp.raft.raftState.getLastApplied.spec : Prop :=
  ∀ (r : Loc) (rc : RCtx GF) (a : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ appliedCell r rc ∗
     monoNatAuthOwn rc.names.applied (1 : Qp).half a }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastApplied")) (Val #()))
  {{ (x : w64), RET #x; ⌜uint.nat x = a⌝ ∗ monoNatAuthOwn rc.names.applied (1 : Qp).half a }}

end spec

end Perennial
