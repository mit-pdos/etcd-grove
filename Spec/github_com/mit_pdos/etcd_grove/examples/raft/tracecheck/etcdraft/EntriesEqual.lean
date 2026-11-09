/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `EntriesEqual(a, b)`: `a = b` (sequences of entries).
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

/-- `EntriesEqual(a, b)`: `a = b`. -/
abbrev EntriesEqual.spec : Prop :=
  ∀ (al : GoSlice) (a : List Entry) (bl : GoSlice) (b : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      logRO al a ∗ logRO bl b }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual)) (Val #al)) (Val #bl))
  {{ RET #(decide (a = b)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
