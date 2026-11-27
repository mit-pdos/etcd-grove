/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__Barrier.lean (241f27e).
-/
/-
`raft.(*Raft).Barrier`'s spec (client-facing, stage 2; notes/stage2-plan.md D3).
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

/-- `(*Raft).Barrier(timeout)` (stage 2), for a client holding a snapshot `sc` taken before the call
(`histLb`): returns a future (`futWait`) whose `Error()` is `nil` only with `barrierOk`: `i` led
some `T` at a snapshot after `sc`, its barrier entry at `b > len0 T` was appended after `sc` and
committed, every voter's durable prefix at `sc` is below `b`, and the FSM had processed some
`s ≥ b` (`fsmAt`).
Why it is true of the code: the `LogBarrier` future goes on `applyCh` (`applyP`, barrier case), or
`errorFuture{ErrEnqueueTimeout}` is returned; the leader loop dispatches it as an entry of its term
(`leaderAppend_upd`, after `sc`: `gprot.srvOwn_now`), and when it is committed, `processLogs`
sends it to the FSM goroutine in a batch; `runFSM` answers it after applying every entry before it
(`fsmAt` for its index), with `gprot.barrier_bound` (the entry is committed: `CIdx`); any other
path (not leader, leadership lost, transfer in progress) answers an error. -/
abbrev github_com.hashicorp.raft.Raft.Barrier.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (sc : Snap) (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ histLb γ sc }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"Barrier")) (Val #tmo))
  {{ (fi : GoInterface), RET #fi; futWait fi (barrierQ γ rc i sc) }}

end spec

end Perennial
