/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/logFuture__Response.lean (241f27e).
-/
/-
`raft.(*logFuture).Response`'s spec (raft-internal interface, notes/raft-iface.md). The `response` field.
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

/-- `(*logFuture).Response`: The `response` field. -/
abbrev github_com.hashicorp.raft.logFuture.Response.spec : Prop :=
  ∀ (f : Loc) (r : GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ f.[logFuture, go!"response"] ↦{dq} r }}
    (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"Response")) (Val #()))
  {{ RET #r; f.[logFuture, go!"response"] ↦{dq} r }}

end spec

end Perennial
