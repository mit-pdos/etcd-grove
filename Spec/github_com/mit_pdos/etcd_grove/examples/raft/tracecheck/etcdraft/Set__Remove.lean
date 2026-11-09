/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Remove(id)`: `s \ {id}` (`SetIds.remove`).
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

/-- `s.Remove(id)`: a fresh set holding `s \ {id}`. -/
abbrev Set.Remove.spec : Prop :=
  ∀ (sl : GoSlice) (s : SetIds) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      setRO sl s }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set'.ty @!! go!"Remove")) (Val #id))
  {{ (u : GoSlice), RET #u; setRO u (s.remove (uint.nat id)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
