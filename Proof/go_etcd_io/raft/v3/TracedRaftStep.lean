/-
Lean-first (no Rocq counterpart). **`raft.Step` on the capability: the statement** (2026-11-10, trace-check
Q8 stage 1 slice 13, `notes/decisions.md`, "Q8 stage 1 (slice 13)"). Not proved: a definition, the target
of piece 2 of the plan.

`raft.Step.spec` is one spec for both modes: the caller's resources `R` through the gates of the path
(`stepGates`) and the closing wand (`stepClose`), which since slice 13 learns the code's end state on the
types a traced node steps (`StepEnd`). An untraced caller supplies them from the struct's nil logger
(`stepBundle_none`, `TracedUntracedRaftStep.lean`). A traced caller supplies them from the capability
(`trCapB`) in the idle phase at the state the step starts in, and gets the capability back in the idle
phase at the state `Step` returns: that is **`stepBundle_traced.statement`** below, the traced
counterpart of `stepBundle_none`; with `raft.Step.spec` it gives `raft.Step`'s traced triple (the
capability in, `SimIdle C s`, and out, `SimIdle C s'`), as `raft.Step.untraced` follows from
`stepBundle_none`.

What only the node API can supply is premised: the received message's token (`recvTokOf`: its
specification message in flight, for a traced type), its numbers (`MsgTrOk`, from `isRaftMsg`), the
terms' bound (`termLB`'s, as a pure bound), the receipts' fit (`readyFits`', for
`ownRaftGhost_traceBound`); and the traced node's configuration (`TracedConfigOk`: pre-vote and
check-quorum off) and message types (`StepEndTy`).

**Not derivable as the specs stand, on the paths that broadcast** (slice 13's finding, the decisions
entry): a leader's heartbeats (`MsgBeat`), a proposal's appends (`MsgProp`), a commit's appends and
`sendAppend`'s flow control (`MsgAppResp`, `MsgHeartbeatResp`), a won election's appends (`MsgVoteResp`)
and a campaign's vote requests (`MsgHup`): each send line adds its message to the node's pending share,
but the step functions' specs give the messages queued only up to `ReplSends`/`HupOkC` (`StepEnd`'s
`ms` existential), and a gate's resource is not indexed by the outbox, so the closing wand cannot
equate the share with the outbox (`SimIdle`'s `P = pendAbs …`). The single-reply paths (a follower's
or candidate's `MsgApp`/`MsgHeartbeat`, a vote request's answer, a stale message, a vote response
without a win, the ignored types) are not blocked by it.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRecvGate
public import Proof.go_etcd_io.raft.v3.LemmasStepGates

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section traced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The received message's token, traced** (the node API's, from the transport): for a message of a
traced type, its specification message (`msgAbs` at the cluster's voters) in flight under some token
`k` (`inFlight`, which the receive line consumes: `trCapB_hookGateRecv`); nothing for another type. -/
def recvTokOf (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8) : IProp GF :=
  iprop(∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
    ∃ (tn : TraceNames) (k : Nat) (ma : Etcdraft.Msg), traceDir γd tn ∗
      ⌜TraceSim.msgAbs tn.voters tn.voters.length (absMsg ty m ents ctx) = some ma⌝ ∗ inFlight tn k ma)

/-- **`raft.Step`'s resources from the capability** (the statement; see the header): at a traced node
(`s.gh.tr = some γd`) idle at `s`, the capability, the received message's token and the node's
premises give, after an update, resources `R` with `Step`'s gates for the message and the closing wand
whose result is the capability idle at the end state `s'` the wand is given. -/
abbrev stepBundle_traced.statement : Prop :=
  ∀ (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop),
  s.gh.tr = some γd →
  -- a traced node's configuration (`TracedConfigOk`) and message types
  s.prevote = false → s.cq = false → StepEndTy m.Type' → NStateWf s →
  -- the numbers the lines read (`TraceEv.Ok`): the terms (`termLB`'s bound at the node API), the
  -- message's (`isRaftMsg`'s `MsgTrOk`), the receipts' fit (`readyFits`)
  uint.Z s.term + 1 < traceNumBound → uint.Z m.Term' < traceNumBound →
  (∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx)) →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  (trCapB s.gh.tr γ r id c true (fun C => SimIdle C s) Λ ∗ recvTokOf γd m ents ctx : IProp GF) ⊢
    |={⊤}=> ∃ R : StepG GF, R.G ∗ stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s R) ∗
      stepClose γ md c id m ents ctx s R (fun s' => trCapB s.gh.tr γ r id c true (fun C => SimIdle C s') Λ)

end traced

end EtcdGrove
end Perennial
