/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Union(t)`: `s ∪ t` (`SetIds.union`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

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

/-- `s.Union(t)`: a fresh set holding `s ∪ t`. -/
abbrev Set.Union.spec : Prop :=
  ∀ (sl : GoSlice) (s : SetIds) (tl : GoSlice) (t : SetIds),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      setRO sl s ∗ setRO tl t }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set'.ty @!! go!"Union")) (Val #tl))
  {{ (u : GoSlice), RET #u; setRO u (s.union t) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
