/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.becomeLeaderIfLogged(ts, i)`, `BecomeLeaderIfLogged(i)`.
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

/-- `t.becomeLeaderIfLogged(ts, i)`, of a server of the state (its granted votes fewer than `2^62`,
`BecomeLeader`'s premise): `tr.becomeLeaderIfLogged ts i`'s successors. -/
abbrev Trace.becomeLeaderIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ (ts.s.s (uint.nat i)).votesGranted.length < 2 ^ 62⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"becomeLeaderIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; statesOut out (tr.becomeLeaderIfLogged ts (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
