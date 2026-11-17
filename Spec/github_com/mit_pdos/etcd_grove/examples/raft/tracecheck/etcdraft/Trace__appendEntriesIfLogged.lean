/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `t.appendEntriesIfLogged(ts, i, j, b, e)`, `AppendEntriesIfLogged(i, j, <<b, e>>)`.
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

/-- `t.appendEntriesIfLogged(ts, i, j, b, e)`, of a server `i` of a state whose pending bag the Go's
`Bag` handles (`Bag.Ok`), the range's ends in `(-2^62, 2^62)` (`AppendEntries`'s premises), where the
Lean evaluates (`= .ok sts`: the Go's `SubSeq` panics where TLC fails): `sts`. -/
abbrev Trace.appendEntriesIfLogged.spec : Prop :=
  ∀ (t : Loc) (tr : Trace) (g : G.TState) (ts : TState) (i j b e : w64) (sts : List State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      traceRO t tr ∗ tstateRO g ts ∗
      ⌜1 ≤ ts.l ∧ uint.nat i ∈ ts.s.server ∧ ts.s.pendingMessages.Ok ∧
        -2 ^ 62 < sint.Z b ∧ sint.Z b < 2 ^ 62 ∧ -2 ^ 62 < sint.Z e ∧ sint.Z e < 2 ^ 62 ∧
        tr.appendEntriesIfLogged ts (uint.nat i) (uint.nat j) (sint.Z b) (sint.Z e) = .ok sts⌝ }}
    (App (App (App (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace.ty
      @!! go!"appendEntriesIfLogged")) (Val #g)) (Val #i)) (Val #j)) (Val #b)) (Val #e))
  {{ (out : GoSlice), RET #out; statesOut out sts }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
