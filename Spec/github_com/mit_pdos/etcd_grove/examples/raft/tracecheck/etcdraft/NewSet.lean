/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `NewSet(ids...)`: the set of `ids`
(`SetIds.mk`).
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

/-- `NewSet(ids...)`: a fresh set holding `SetIds.mk ids`, read-only like every set. -/
abbrev NewSet.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      sl ↦*□ xs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewSet)) (Val #sl))
  {{ (s : GoSlice), RET #s; setRO s (SetIds.mk (xs.map (fun x => uint.nat x))) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
