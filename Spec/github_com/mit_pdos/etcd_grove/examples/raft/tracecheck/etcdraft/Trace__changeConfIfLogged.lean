/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.changeConfIfLogged(ts, i, j, action)`,
`AddNewServerIfLogged(i, j)`, `AddLearnerIfLogged(i, j)`, `DeleteServerIfLogged(i, j)`, at a line that
is not a `ChangeConf`.
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

/-- `t.changeConfIfLogged(ts, i, j, action)`, at a line that is not a `ChangeConf`: no successor, as
`tr.changeConfIfLogged`'s. Configuration changes are outside what the checker's proof needs (the
workload proposes none: premise P3 of `notes/trace-validation-sim.md`), so `AddNewServer`,
`AddLearner` and `DeleteServer` have no spec and this one excludes the case
(`notes/trace-validation-plan.md`, layer C). -/
abbrev Trace.changeConfIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i j : w64) (action : GoString) (a : String),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ strRel action a ∧ (tr.line ts.l).ev.name ≠ "ChangeConf"⌝ }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"changeConfIfLogged")) (Val #g)) (Val #i)) (Val #j)) (Val #action))
  {{ (out : GoSlice), RET #out; statesOut out (tr.changeConfIfLogged ts (uint.nat i) (uint.nat j) a) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
