/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `indexOf(tss, ts)`, the position of a state equal to `ts` (`memEq`).
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

/-- `indexOf(tss, ts)`: the position of the first state of `tss` equal to `ts` by TLC's view
(`TState.eq`), or `-1` (so `>= 0` exactly where `memEq xs ts`). -/
abbrev indexOf.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (gs : List G.TState) (xs : List TState) (g : G.TState) (ts : TState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      sl ↦*{dq} gs ∗ ([∗list] h;x ∈ gs;xs, tstateRO h x) ∗ tstateRO g ts }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.indexOf)) (Val #sl))
      (Val #g))
  {{ (k : w64), RET #k; sl ↦*{dq} gs ∗
      ⌜sint.Z k = match xs.findIdx? (fun us => us.eq ts) with | some i => (i : Int) | none => -1⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
