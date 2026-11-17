/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `ParseRole(s)`.
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

/-- `ParseRole(s)`: the role `s` itself. -/
abbrev ParseRole.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.ParseRole)) (Val #s))
  {{ RET #s; True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
