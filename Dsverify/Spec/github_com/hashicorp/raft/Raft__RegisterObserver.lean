/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__RegisterObserver.lean (241f27e).
-/
/-
`raft.(*Raft).RegisterObserver`'s spec (raft-internal interface, notes/raft-iface.md). Adds an observer meeting `obsOk` (under the observers' write lock).
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

/-- `(*Raft).RegisterObserver`: Adds an observer meeting `obsOk` (under the observers' write lock). -/
abbrev github_com.hashicorp.raft.Raft.RegisterObserver.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ obsOk γ i r o }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"RegisterObserver")) (Val #o))
  {{ RET #(); True }}

end spec

end Perennial
