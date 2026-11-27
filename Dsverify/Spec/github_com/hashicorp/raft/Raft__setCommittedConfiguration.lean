/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setCommittedConfiguration.lean (241f27e).
-/
/-
`raft.(*Raft).setCommittedConfiguration`'s spec (raft-internal interface, notes/raft-iface.md). Called by the main goroutine (it holds `configurations`).
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

/-- `(*Raft).setCommittedConfiguration`: Called by the main goroutine (it holds `configurations`). -/
abbrev github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec : Prop :=
  ∀ (r : Loc) (c0 l : Configuration) (i0 li : w64) (c : Configuration) (ci : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l li }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setCommittedConfiguration")) (Val #c)) (Val #ci))
  {{ RET #(); r.[Raft, go!"configurations"] ↦ configurations.mk c ci l li }}

end spec

end Perennial
