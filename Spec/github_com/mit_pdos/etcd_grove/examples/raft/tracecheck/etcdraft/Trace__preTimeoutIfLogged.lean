/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.preTimeoutIfLogged(ts, i)`,
`PreTimeoutIfLogged(i)`.
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

/-- `t.preTimeoutIfLogged(ts, i)`, of a server `i` of a state whose `PreVote` is off (`PreTimeout`'s
premise: pre-vote is outside what the checker's proof needs, `NewTrace` sets the flag off and every
action keeps it): `tr.preTimeoutIfLogged ts i`'s successors (none). -/
abbrev Trace.preTimeoutIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ ts.s.preVote = false⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"preTimeoutIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; statesOut out (tr.preTimeoutIfLogged ts (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
