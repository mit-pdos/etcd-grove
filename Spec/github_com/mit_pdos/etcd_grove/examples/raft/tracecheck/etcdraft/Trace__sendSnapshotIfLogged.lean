/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.sendSnapshotIfLogged(ts, i, j, index)`,
`SendSnapshotIfLogged(i, j, index)`, at a line that is not a snapshot's.
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

/-- `t.sendSnapshotIfLogged(ts, i, j, index)`, at a line whose message is not a `MsgSnap`: no
successor, as `tr.sendSnapshotIfLogged`'s. Snapshots are outside what the checker's proof needs (the
workload never compacts, so raft never sends one: premise P2 of `notes/trace-validation-sim.md`), so
`SendSnapshot` has no spec and this one excludes the case (`notes/trace-validation-plan.md`, layer C). -/
abbrev Trace.sendSnapshotIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i j index : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ (tr.line ts.l).ev.msg.map EventMsg.type ≠ some "MsgSnap"⌝ }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"sendSnapshotIfLogged")) (Val #g)) (Val #i)) (Val #j)) (Val #index))
  {{ (out : GoSlice), RET #out;
      ⌜tr.sendSnapshotIfLogged ts (uint.nat i) (uint.nat j) (sint.Z index) = .ok []⌝ ∗ statesOut out [] }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
