/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.applySimpleConfChangeIfLogged(ts, i)`,
`ApplySimpleConfChangeIfLogged(i)`.
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

/-- `t.applySimpleConfChangeIfLogged(ts, i)`, of a server `i` of the state (`ApplySimpleConfChange`'s
premises: its log below `2^62`, the reconfiguration count below `2^63 - 1`), where the Lean evaluates
(`= .ok sts`: the Go panics with an `EvalError` where TLC fails, a commit index past the log): `sts`. -/
abbrev Trace.applySimpleConfChangeIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i : w64) (sts : List State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ (ts.s.s (uint.nat i)).log.length < 2 ^ 62 ∧
        ts.s.reconfigCount + 1 < 2 ^ 63 ∧ tr.applySimpleConfChangeIfLogged ts (uint.nat i) = .ok sts⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"applySimpleConfChangeIfLogged")) (Val #g)) (Val #i))
  {{ (out : GoSlice), RET #out; statesOut out sts }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
