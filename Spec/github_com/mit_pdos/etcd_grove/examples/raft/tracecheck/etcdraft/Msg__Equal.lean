/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `m.Equal(n)`: `m = n`.
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

/-- `m.Equal(n)`: `m = n` (structural, the entries included; the messages' relation is canonical:
a shape's absent fields are at their default on both sides). -/
abbrev Msg.Equal.spec : Prop :=
  ∀ (p : Loc) (m : Msg) (q : Loc) (n : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      msgRO p m ∗ msgRO q n }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Msg.ty @!! go!"Equal")) (Val #q))
  {{ RET #(decide (m = n)); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
