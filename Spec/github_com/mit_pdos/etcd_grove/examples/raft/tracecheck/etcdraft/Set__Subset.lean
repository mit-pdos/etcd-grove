/-
Lean-first (no Rocq counterpart). Layer C (2026-11-08): `Set.Subset(t)`: whether every element of
the set is in `t` (`IsQuorum`'s first half, which `Timeout` calls with PreVote).
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

/-- `s.Subset(t)`: `s ⊆ t`. -/
abbrev Set.Subset.spec : Prop :=
  ∀ (sl : GoSlice) (s : SetIds) (tl : GoSlice) (t : SetIds),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      setRO sl s ∗ setRO tl t }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set'.ty @!! go!"Subset"))
      (Val #tl))
  {{ RET #(s.subset t); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
