/-
Lean-first (no Rocq counterpart). Draft (2026-11-08), layer C of `notes/trace-validation-plan.md`.

`CheckTrace(t, invariants)` (`examples/raft/tracecheck/etcdraft/check.go`): TLC's check of the
trace `t` against `Traceetcdraft.tla` (its breadth-first search, line by line, deduplicated by the
view `<<vars, l>>`, the invariants checked at every state reached when `invariants`; an evaluation
TLC would fail is a failure). Its spec: the Lean transcription's `checkTrace` (`Tla/Check.lean`)
is what it computes, on the fields it records (`resultRel`); so `Result.TLCOK()` is
`(checkTrace tr invariants).tlcOK`, and with `NewTrace`'s spec, `traceAccepts` is `Main`'s check.
The trace is read, not written (`traceRO`).
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
  (∀ ln ∈ tr.lines, ln.ev.Bounded) → tr.lines.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckTrace))
      (Val #t)) (Val #invariants))
  {{ (r : G.Result), RET #r; ⌜resultRel r (checkTrace tr invariants)⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
