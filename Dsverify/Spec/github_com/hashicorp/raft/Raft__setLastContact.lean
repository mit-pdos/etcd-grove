/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setLastContact.lean (241f27e).
-/
/-
`raft.(*Raft).setLastContact`'s spec (raft-internal interface, notes/raft-iface.md). Under `lastContactLock` (write lock: no thread token).
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

/-- `(*Raft).setLastContact`: Under `lastContactLock` (write lock: no thread token). -/
abbrev github_com.hashicorp.raft.Raft.setLastContact.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastContact")) (Val #()))
  {{ RET #(); True }}

end spec

end Perennial
