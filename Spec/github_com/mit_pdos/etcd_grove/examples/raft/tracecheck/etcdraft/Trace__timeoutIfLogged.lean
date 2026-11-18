/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.timeoutIfLogged(ts, i)`, `TimeoutIfLogged(i)`.
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

/-- `t.timeoutIfLogged(ts, i)`, of a server of the state whose term is below `2^63 - 1` and whose
granted votes are fewer than `2^62` (`Timeout`'s premises): `tr.timeoutIfLogged ts i`'s successors. -/
abbrev Trace.timeoutIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ (ts.s.s (uint.nat i)).currentTerm < 2 ^ 63 - 1 ∧
        (ts.s.s (uint.nat i)).votesGranted.length < 2 ^ 62⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"timeoutIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; statesOut out (tr.timeoutIfLogged ts (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
