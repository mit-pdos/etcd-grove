/-
Port of `election_proof/spec_traceReceiveMessage.v` (feb5c73d4).
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

/-- `traceReceiveMessage(r, m)`: reads `r.traceLogger` and returns when it is nil; otherwise, for a
message type it traces (`MsgApp`, `MsgHeartbeat`, `MsgSnap`, `MsgAppResp`, `MsgHeartbeatResp`,
`MsgVote`, `MsgVoteResp`), sleeps 1ms (`time.Sleep`) and logs the receipt (`traceEvent`, with the
message); for any other type nothing.

One spec for both modes (Q8 stage 1, slice 4, 2026-11-09), as `traceSendMessage.spec`, with the
receive hook's gate (`recvGate`, the Draft's). The Draft's `traceReceiveMessage.tracedSpec` follows
(`TracedHooks.lean`). Until slice 4 the spec was the untraced case alone (`⌜TraceLoggerOk tl⌝`,
giving `True`), which is `traceReceiveMessage.untraced` (`TracedUntraced.lean`). -/
abbrev traceReceiveMessage.spec : Prop :=
  ∀ (r ml : Loc) (tl : GoInterface) (tr : Option GName) (oE : Option (TraceEv → Prop)) (Q R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜tr = none → TraceLoggerOk tl⌝ ∗
      trOwn tr iprop(∃ (c : CfgM) (id : w64) (s : NState) (P : IProp GF) (a : MsgArg),
        P ∗ RaftLend P c r id s ∗ MsgLend P ml (some a) ∗
        ⌜mtypeOf a.ms.msg.Type' ≠ some .snap ∧ oE = recvGate id s c a.ms⌝ ∗ (P -∗ R)) ∗
      TraceFireOpt tr tl oE Q }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); trOwn tr R ∗ Q }}

end spec

end EtcdGrove
end Perennial
