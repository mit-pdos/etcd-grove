/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.advanceCommitIndexIfLogged(ts, i)`, `AdvanceCommitIndexIfLogged(i)`.
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

/-- `t.advanceCommitIndexIfLogged(ts, i)`, of a server of the state whose configuration and log are
fewer than `2^62` (`AdvanceCommitIndex`'s premises): `tr.advanceCommitIndexIfLogged ts i`'s
successors. -/
abbrev Trace.advanceCommitIndexIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ (ts.s.getConfig (uint.nat i)).length < 2 ^ 62 ∧
        (ts.s.s (uint.nat i)).log.length < 2 ^ 62⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"advanceCommitIndexIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; statesOut out (tr.advanceCommitIndexIfLogged ts (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
