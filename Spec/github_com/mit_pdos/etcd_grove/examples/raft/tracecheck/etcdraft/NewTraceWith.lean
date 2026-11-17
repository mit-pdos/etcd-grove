/-
Lean-first (no Rocq counterpart). Layer C of `notes/trace-validation-plan.md` (2026-11-09).

`NewTraceWith(events, preVote, checkQuorum)` (`examples/raft/tracecheck/etcdraft/trace.go`): the
trace specification of `events` for raft's `PreVote` and `CheckQuorum`, or an error where TLC would
fail reading it. Its spec is `NewTrace`'s for any flags: for bounded, read-only, ASCII events
(`NewTrace`'s premises), it returns an error exactly when the Lean's `newTraceWith` refuses, and
otherwise a trace holding `newTraceWith`'s (`traceHeapRO`: `traceRO` without `Trace.Valid`, which is
about `newTrace`, the flags off; `NewTrace`'s proof adds it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceBuild

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
abbrev NewTraceWith.spec : Prop :=
  ∀ (sl : GoSlice) (evs : List Event) (pv cq : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      eventsRO sl evs ∗
      ⌜(∀ e ∈ evs, e.Bounded) ∧ (evs.length : Int) < numBound ∧ Event.BootLogsOk evs⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewTraceWith))
      (Val #sl)) (Val #pv)) (Val #cq))
  {{ (t : Loc) (err : GoInterface), RET (PairV #t #err);
      match newTraceWith evs pv cq with
      | .error _ => ⌜err ≠ interface.nil⌝
      | .ok tr => ⌜err = interface.nil⌝ ∗ traceHeapRO t tr }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
