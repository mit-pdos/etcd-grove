/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.heartbeatIfLogged(ts, i, j)`, `HeartbeatIfLogged(i, j)`.
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

/-- `t.heartbeatIfLogged(ts, i, j)`, of a server `i` of a state whose pending bag the Go's `Bag`
handles (`Heartbeat`'s premises), where the Lean evaluates (`= .ok sts`): `sts`. -/
abbrev Trace.heartbeatIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i j : w64) (sts : List State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ ts.s.pendingMessages.Ok ∧
        tr.heartbeatIfLogged ts (uint.nat i) (uint.nat j) = .ok sts⌝ }}
    (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"heartbeatIfLogged")) (Val #g)) (Val #i)) (Val #j))
  {{ (out : GoSlice), RET #out; statesOut out sts }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
