/-
Lean-first (no Rocq counterpart): `makeTracingMessage` (`state_trace.go`), a traced event's message
(Q8 stage 1, slice 2, 2026-11-09).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedCap

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

/-- `makeTracingMessage(m)` of a nil message (a node event's, `traceNodeEvent`): nil.

Only the nil case so far (Q8 stage 1, slice 2): a message's case names its type
(`m.GetType().String()`), whose trust-boundary axiom (`raftpb.MessageType.String`) gives some
string, not the type's name the traced send and receive lines need (the plan's Q9, the user's); it
is to be added as a second conjunct, as the getters' specs state their nil case beside the other. -/
abbrev makeTracingMessage.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions makeTracingMessage [])) (Val #(null : Loc)))
  {{ RET #(null : Loc); True }}

end spec

end EtcdGrove
end Perennial
