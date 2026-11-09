/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.clientRequestIfLogged(ts, i, v)`, `ClientRequestIfLogged(i, v)`.
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

/-- `t.clientRequestIfLogged(ts, i, v)`, of a server of the state: `tr.clientRequestIfLogged ts i v`'s
successors. -/
abbrev Trace.clientRequestIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗ ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"clientRequestIfLogged")) (Val #g)) (Val #i)) (Val #v))
  {{ (out : GoSlice), RET #out; statesOut out (tr.clientRequestIfLogged ts (uint.nat i) (sint.Z v)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
