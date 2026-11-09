/-
Lean-first (no Rocq counterpart). Draft (2026-11-08), layer C of `notes/trace-validation-plan.md`.

`NewTrace(events)` (`examples/raft/tracecheck/etcdraft/trace.go`): the trace specification of
`events`, as `Traceetcdraft.tla` reads it (its constants `TraceLog`, `TraceServer`,
`TraceInitServer`, `BootstrapLogIndices`, and `TraceInit`), or an error where TLC would fail
reading it. Its spec: the Lean transcription's `newTrace` (`Tla/Trace.lean`) is what it computes.
For events with numbers far from overflow (`Event.Bounded`), bootstrap logs Go can allocate
(`Event.BootLogsOk`), read-only (`eventsRO`: the trace keeps pointers into them) and with ASCII
strings (`strRel`, `Rep.lean`: raft's names, roles and ids are), it returns an error exactly when `newTrace` refuses, and otherwise a trace (`traceRO`,
read-only) holding `newTrace`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- See the file header. -/
abbrev NewTrace.spec : Prop :=
  ∀ (sl : GoSlice) (evs : List Event),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      eventsRO sl evs ∗
      ⌜(∀ e ∈ evs, e.Bounded) ∧ (evs.length : Int) < numBound ∧ Event.BootLogsOk evs⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewTrace)) (Val #sl))
  {{ (t : Loc) (err : GoInterface), RET (PairV #t #err);
      match newTrace evs with
      | .error _ => ⌜err ≠ interface.nil⌝
      | .ok tr => ⌜err = interface.nil⌝ ∗ traceRO t tr }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
