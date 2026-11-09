/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.restartIfLogged(ts, i)`,
`RestartIfLogged(i)`, at a line that is not an `InitState`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

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

/-- `t.restartIfLogged(ts, i)`, at a line that is not an `InitState`: no successor, as
`tr.restartIfLogged`'s. Restarts are outside what the checker's proof needs (the workload restarts no
node: premise P1 of `notes/trace-validation-sim.md`, `InitState` only at bootstrap, where `TraceNext`
steps over the line without the actions), so `Restart` has no spec and this one excludes the case
(`notes/trace-validation-plan.md`, layer C). -/
abbrev Trace.restartIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜1 ≤ ts.l ∧ (tr.line ts.l).ev.name ≠ "InitState"⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"restartIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; ⌜tr.restartIfLogged ts (uint.nat i) = .ok []⌝ ∗ statesOut out [] }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
