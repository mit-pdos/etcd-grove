/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__restoreFromCommittedLogs.lean (241f27e).
-/
/-
`raft.(*Raft).restoreFromCommittedLogs`'s spec (API-internal): `RestoreCommittedLogs` is false, nothing happens.
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

/-- `(*Raft).restoreFromCommittedLogs` with `RestoreCommittedLogs = false`: returns nil. -/
abbrev github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     r.[Raft, go!"RestoreCommittedLogs"] ↦□ false }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"restoreFromCommittedLogs")) (Val #()))
  {{ RET #interface.nil; True }}

end spec

end Perennial
