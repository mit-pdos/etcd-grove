/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.ignoreInLeaseIfLogged(ts)`,
`\E m \in DOMAIN messages : IgnoreInLeaseIfLogged(m)`.
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

/-- `t.ignoreInLeaseIfLogged(ts)`, of a state whose `CheckQuorum` is off (`IgnoreInLease`'s premise:
check-quorum is outside what the checker's proof needs, `NewTrace` sets the flag off and every action
keeps it): `tr.ignoreInLeaseIfLogged ts`'s successors (none). -/
abbrev Trace.ignoreInLeaseIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜1 ≤ ts.l ∧ ts.s.checkQuorum = false⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"ignoreInLeaseIfLogged")) (Val #g))
  {{ (out : GoSlice), RET #out; statesOut out (tr.ignoreInLeaseIfLogged ts) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
