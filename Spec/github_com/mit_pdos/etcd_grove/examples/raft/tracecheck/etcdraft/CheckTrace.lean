/-
Lean-first (no Rocq counterpart). Draft (2026-11-08), layer C of `notes/trace-validation-plan.md`.

`CheckTrace(t, invariants)` (`examples/raft/tracecheck/etcdraft/check.go`): TLC's check of the
trace `t` against `Traceetcdraft.tla` (its breadth-first search, line by line, deduplicated by the
view `<<vars, l>>`, the invariants checked at every state reached when `invariants`; an evaluation
TLC would fail is a failure). Its spec: what it returns is the result the Lean transcription's
`CheckTraceRel` (`Tla/Check.lean`, the search as a relation, without fuel: Q7, the user's choice
2026-11-08) relates the trace to, on the fields it records (`resultRel`); so `Result.TLCOK()` holds
only of a trace the relation accepts, and with `NewTrace`'s spec, `TraceAccepts` is `Main`'s check.
Partial correctness: a search that never ends returns nothing.
The trace is read, not written (`traceRO`, which carries what `NewTrace` establishes: the Go's search
relies on that, review round 1 of layer C, F1).
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
abbrev CheckTrace.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (invariants : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckTrace))
      (Val #t)) (Val #invariants))
  {{ (r : G.Result), RET #r; ∃ lr, ⌜CheckTraceRel tr invariants lr ∧ resultRel r lr⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
