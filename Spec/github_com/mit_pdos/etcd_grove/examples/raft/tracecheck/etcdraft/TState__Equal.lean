/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `ts.Equal(us)`, TLC's view `<<vars, l>>`.
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

/-- `ts.Equal(us)`: `ts.eq us`. -/
abbrev TState.Equal.spec : Prop :=
  ∀ (g : G.TState) (ts : TState) (h : G.TState) (us : TState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      tstateRO g ts ∗ tstateRO h us }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TState.ty
      @!! go!"Equal")) (Val #h))
  {{ RET #(ts.eq us); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
