/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `e.Equal(f)`: `e = f`.
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

/-- `e.Equal(f)`: `e = f`. -/
abbrev Entry.Equal.spec : Prop :=
  ∀ (e : G.Entry) (x : Entry) (f : G.Entry) (y : Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      entryRO e x ∗ entryRO f y }}
    (App (Val (e @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry.ty @!! go!"Equal")) (Val #f))
  {{ RET #(decide (x = y)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
