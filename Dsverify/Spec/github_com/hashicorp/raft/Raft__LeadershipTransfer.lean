/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__LeadershipTransfer.lean (241f27e).
-/
/-
`raft.(*Raft).LeadershipTransfer`'s spec (client-facing, stage 2; notes/stage2-plan.md D6).
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

/-- `(*Raft).LeadershipTransfer()` (stage 2): returns a future whose `Error()` may be called once
(any answer; no protocol facts: a transfer changes no protocol rule, it only makes the target start
an election, `timeoutNow`).
Why it is true of the code: `protocolVersion = 3`; `initiateLeadershipTransfer(nil, nil)` sends a
`*leadershipTransferFuture` with no target on `leadershipTransferCh` (`ltfP`) or returns
`errorFuture{ErrEnqueueTimeout}` (the send does not block). -/
abbrev github_com.hashicorp.raft.Raft.LeadershipTransfer.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"LeadershipTransfer")) (Val #()))
  {{ (fi : GoInterface), RET #fi; futWait fi (fun _ => iprop(True)) }}

end spec

end Perennial
