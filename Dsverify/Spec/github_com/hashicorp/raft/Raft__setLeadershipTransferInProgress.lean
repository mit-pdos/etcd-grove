/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setLeadershipTransferInProgress.lean (241f27e).
-/
/-
`raft.(*Raft).setLeadershipTransferInProgress`'s spec (internal to the leader part of the main goroutine, MAIN-L, stage 2).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs

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

/-- `(*Raft).setLeadershipTransferInProgress(v)`: stores `1` or `0` in the atomic `ltipCell`
(no fact about its value is needed). -/
abbrev github_com.hashicorp.raft.Raft.setLeadershipTransferInProgress.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLeadershipTransferInProgress")) (Val #b))
  {{ RET #(); True }}

end spec

end Perennial
