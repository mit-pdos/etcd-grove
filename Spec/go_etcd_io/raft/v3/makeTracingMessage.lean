/-
Lean-first (no Rocq counterpart): `makeTracingMessage` (`state_trace.go`), a traced event's message
(Q8 stage 1, slice 2, 2026-11-09: the nil case; slice 4: the message's).
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `makeTracingMessage(m)`: of a nil message (a node event's, `traceNodeEvent`), nil; of a message
holding `ms` (read through its getters, given back), a new read-only `TracingMessage` holding
`traceMsgOf ms`: the type's name (`raftpb.msgTypeString`, the exact `MessageType.String` of Q9), the
term, sender, receiver and vote in decimal (`decStr`), the entry count, log term and index (for a
`MsgSnap`: its snapshot's index, `0`, `0`), commit, reject and hint.

(Q8 stage 1, slice 2: the nil case only, the type's name then being a trust-boundary axiom's some
string; slice 4, after Q9: the message's case.) -/
abbrev makeTracingMessage.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions makeTracingMessage [])) (Val #(null : Loc)))
  {{ RET #(null : Loc); True }} ∧
  ∀ (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ msgPtsC l dq dqe cap ms }}
    (App (Val #(functions makeTracingMessage [])) (Val #l))
  {{ (p : Loc), RET #p; msgPtsC l dq dqe cap ms ∗ tracingMsgRep p (some (traceMsgOf ms)) }}

end spec

end EtcdGrove
end Perennial
