/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Add(id)`: `s ∪ {id}` (`SetIds.add`).
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

/-- `s.Add(id)`: a fresh set holding `s ∪ {id}`. -/
abbrev Set.Add.spec : Prop :=
  ∀ (sl : GoSlice) (s : SetIds) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      setRO sl s }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set'.ty @!! go!"Add")) (Val #id))
  {{ (u : GoSlice), RET #u; setRO u (s.add (uint.nat id)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
