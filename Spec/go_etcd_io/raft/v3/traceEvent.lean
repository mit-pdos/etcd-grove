/-
Lean-first (no Rocq counterpart): `traceEvent` (`state_trace.go`, translated under the `goose`
tag since 2026-11-08, `notes/trace-validation-hooks.md`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvLogger

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

/-- `traceEvent(evt, r, m, prop)`: reads `r.traceLogger` and returns when it is nil; otherwise
builds the event from `r`'s state and calls the logger's `TraceEvent`. Under `TraceLoggerOk`
(increment 1: the logger is nil) it returns at once, owning nothing but the field, shared. -/
abbrev traceEvent.spec : Prop :=
  ∀ (evt : w64) (r m : Loc) (prop : GoMap) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜TraceLoggerOk tl⌝ }}
    (App (App (App (App (Val #(functions traceEvent [])) (Val #evt)) (Val #r)) (Val #m)) (Val #prop))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
