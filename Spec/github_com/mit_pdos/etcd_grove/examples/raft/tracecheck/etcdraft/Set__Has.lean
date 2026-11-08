/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08, `notes/trace-validation-plan.md`,
"Probe set"): `Set.Has(id)`: whether the set holds `id`.
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

/-- `s.Has(id)`: `id ∈ s`. -/
abbrev Set.Has.spec : Prop :=
  ∀ (sl : GoSlice) (s : SetIds) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      setRO sl s }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set'.ty @!! go!"Has"))
      (Val #id))
  {{ RET #(decide (uint.nat id ∈ s)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
