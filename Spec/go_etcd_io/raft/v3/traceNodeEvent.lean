/-
Lean-first (no Rocq counterpart): `traceNodeEvent` (`state_trace.go`, translated under the `goose`
tag since 2026-11-08, `notes/trace-validation-hooks.md`).
-/
module

public import Spec.go_etcd_io.raft.v3.traceEvent

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

/-- `traceNodeEvent(evt, r)`: `traceEvent(evt, r, nil, nil)`. Under `TraceLoggerOk` (increment 1, `notes/trace-validation-hooks.md`: the logger is nil) it
returns at once, owning nothing but the field, shared (`ownRaftPhysC_traceLogger`). Until
2026-11-08 the translated build was the no-op one (`state_trace_nop.go`) and the spec owned
nothing; increment 2 (`notes/trace-validation-sim.md`) replaces
`TraceLoggerOk` by the logger's contract `isTraceLogger γt`, changing this statement. -/
abbrev traceNodeEvent.spec : Prop :=
  ∀ (evt : w64) (r : Loc) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜TraceLoggerOk tl⌝ }}
    (App (App (Val #(functions traceNodeEvent [])) (Val #evt)) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
