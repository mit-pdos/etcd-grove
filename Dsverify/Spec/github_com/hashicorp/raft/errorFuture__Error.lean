/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/errorFuture__Error.lean (241f27e).
-/
/-
`raft.errorFuture.Error`'s spec (raft-internal interface, notes/raft-iface.md). Its error.
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

/-- `errorFuture.Error`: Its error. -/
abbrev github_com.hashicorp.raft.errorFuture.Error.spec : Prop :=
  ∀ (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (errorFuture.mk e @!! errorFuture.ty @!! go!"Error")) (Val #()))
  {{ RET #e; True }}

end spec

end Perennial
