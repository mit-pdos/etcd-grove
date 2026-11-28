/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/asyncNotifyCh.lean (241f27e).
-/
/-
`raft.asyncNotifyCh`'s spec (raft-internal interface, notes/raft-iface.md). A non-blocking send on a bag channel (the value's resource is dropped if the channel is full).
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

/-- `asyncNotifyCh`: A non-blocking send on a bag channel (the value's resource is dropped if the channel is full). -/
abbrev github_com.hashicorp.raft.asyncNotifyCh.spec : Prop :=
  ∀ (γc : ChanNames) (ch : Loc) (P : Unit → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isChanBag (V := Unit) γc ch P ∗ P () }}
    (App (Val (@! github_com.hashicorp.raft.asyncNotifyCh)) (Val #ch))
  {{ RET #(); True }}

end spec

end Perennial
