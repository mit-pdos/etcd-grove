/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__getLeadershipTransferInProgress.lean (241f27e).
-/
/-
`raft.(*Raft).getLeadershipTransferInProgress`'s spec (internal to the leader part of the main goroutine, MAIN-L). Whether a leadership transfer is in progress (stage 2: the atomic `leadershipTransferInProgress` holds any value; no fact about it).
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

/-- `(*Raft).getLeadershipTransferInProgress`: Whether a leadership transfer is in progress (stage 2: the atomic `leadershipTransferInProgress` holds any value; no fact about it). -/
abbrev github_com.hashicorp.raft.Raft.getLeadershipTransferInProgress.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLeadershipTransferInProgress")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end Perennial
