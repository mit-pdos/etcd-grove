/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/drainNotifyCh.lean (241f27e).
-/
/-
`raft.drainNotifyCh`'s spec (raft-internal interface, notes/raft-iface.md). A non-blocking receive on a bag channel.
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

/-- `drainNotifyCh`: A non-blocking receive on a bag channel. -/
abbrev github_com.hashicorp.raft.drainNotifyCh.spec : Prop :=
  ∀ (γc : ChanNames) (ch : Loc) (P : Unit → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isChanBag (V := Unit) γc ch P }}
    (App (Val (@! github_com.hashicorp.raft.drainNotifyCh)) (Val #ch))
  {{ (b : Bool), RET #b; True }}

end spec

end Perennial
