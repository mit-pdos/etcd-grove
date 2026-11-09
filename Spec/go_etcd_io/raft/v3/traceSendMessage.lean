/-
Port of `election_proof/spec_traceSendMessage.v` (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceSendMessage(r, m)`: reads `r.traceLogger` and returns when it is nil; otherwise, for a
message type it traces (`MsgApp`, `MsgHeartbeat`, `MsgSnap`, `MsgAppResp`, `MsgHeartbeatResp`,
`MsgVote`, `MsgVoteResp`), logs the send (`traceEvent`, with the message and, for a `MsgApp`, the
sender's `Progress` as the properties `match` and `next`); for any other type nothing.

One spec for both modes (Q8 stage 1, slice 4, 2026-11-09), by the caller's mode `tr`, in
`traceEvent`'s lending form: untraced, the nil logger (`tr = none → TraceLoggerOk tl`) and `Q`;
traced, the gate `TraceFireOpt tr tl oE Q` at the events `oE` the send hook's gate gives
(`sendGate`, the Draft's: a `SendEvOf` event of the message's abstraction for a traced type, `none`
for another), and under `trOwn tr`, lent out of the caller's `P` (given back as `R`), raft's state
(`RaftLend`) and the message (`MsgLend`, any fractions), never a snapshot (P2: a snapshot is traced
in Go, the specification's `sendGate` does not). The Draft's `traceSendMessage.tracedSpec`, the state
and the message held apart, follows (`TracedHooks.lean`); `raft.send`, whose message is queued in
raft's struct when the hook runs, would lend both out of `ownRaftPhysCV` (blocked: plan, slice 4).

Until slice 4 the spec was the untraced case alone (`⌜TraceLoggerOk tl⌝`, giving `True`), which is
`traceSendMessage.untraced` (`TracedUntraced.lean`). -/
abbrev traceSendMessage.spec : Prop :=
  ∀ (r ml : Loc) (tl : GoInterface) (tr : Option GName) (oE : Option (TraceEv → Prop)) (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜tr = none → TraceLoggerOk tl⌝ ∗
      trOwn tr iprop(∃ (c : CfgM) (id : w64) (s : NState) (P : IProp GF) (a : MsgArg),
        P ∗ RaftLend P c r id s ∗ MsgLend P ml (some a) ∗
        ⌜mtypeOf a.ms.msg.Type' ≠ some .snap ∧ oE = sendGate id s c a.ms⌝ ∗ (P -∗ R)) ∗
      TraceFireOpt tr tl oE Q }}
    (App (App (Val #(functions traceSendMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); trOwn tr R ∗ Q }}

end spec

end EtcdGrove
end Perennial
