/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__VerifyLeader.lean (241f27e).
-/
/-
`raft.(*Raft).VerifyLeader`'s spec (client-facing, stage 2; notes/stage2-plan.md D2).
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

/-- `(*Raft).VerifyLeader()` (stage 2), for a client holding a snapshot `sc` taken before the call
(`histLb`): returns a future (`futWait`) whose `Error()` is `nil` only with `verifyOk`: `i` led some
`T` at a snapshot after `sc`, the FSM had processed some `s` (`fsmAt`) and every voter's durable
prefix at `sc` is at most `len0 T` or at most `s`.
Why it is true of the code: the future goes on `verifyCh` (or `errorFuture{ErrRaftShutdown}`, never:
`shutdownCh` is never closed); the leader loop registers it at a snapshot after `sc`
(`verifyLeader`), each follower's heartbeat goroutine votes with its response to a heartbeat sent
after (a success is its term witness, fix `d660d8b`), and at a quorum the leader loop applies
`gprot.read_bound_upd` and hands the future to the FSM goroutine behind the batches already sent
(fix `ea6e596`), which answers it with `fsmAt`; any other path answers an error.
(Stage 4: no premise on the number of voters; stage 3 had `2 ≤ |voters|`: with a single voter
`verifyLeader` answered `nil` at once without waiting for the FSM; fix `0c7aa12` sends that case
through `fsmMutateCh` too. The quorum is of the leader's latest configuration at the registration,
the leader's own vote only if it is a voter there, fix `4bb3955`, and only its voters' votes count,
fix `6c3454c`.) -/
abbrev github_com.hashicorp.raft.Raft.VerifyLeader.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (sc : Snap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     histLb γ sc }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"VerifyLeader")) (Val #()))
  {{ (fi : GoInterface), RET #fi; futWait fi (verifyQ γ rc i sc) }}

end spec

end Perennial
