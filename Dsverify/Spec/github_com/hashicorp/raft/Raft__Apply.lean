/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__Apply.lean (241f27e).
-/
/-
`raft.(*Raft).Apply`'s spec (raft-internal interface, notes/raft-iface.md). Submits the command `cmd` (data `d`, read-only from now on) with the client's operation token: returns the client's future (`futureOwn`): an `errorFuture{ErrEnqueueTimeout}` (token kept) or the `*logFuture` sent on `applyCh`.
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

/-- `(*Raft).Apply`: Submits the command `cmd` (data `d`, read-only from now on) with the client's operation token: returns the client's future (`futureOwn`): an `errorFuture{ErrEnqueueTimeout}` (token kept) or the `*logFuture` sent on `applyCh`. -/
abbrev github_com.hashicorp.raft.Raft.Apply.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (cmd : GoSlice) (d : List w8) (n : Nat)
    (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ cmd ↦*□ d ∗ opTok γ d n }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"Apply")) (Val #cmd)) (Val #tmo))
  {{ (fi : GoInterface), RET #fi; futureOwn γ rc fi d n }}

end spec

end Perennial
