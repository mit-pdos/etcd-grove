/-
Lean-first (no Rocq counterpart). Layer C (2026-11-08): `IsQuorum(q, c)`: `q \in Quorum(c)`.
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

/-- `IsQuorum(q, c)`: `q \in Quorum(c)` (`isQuorum`). The sets' sizes below `2^62` (the Go's
`len(q)*2` in `int`). -/
abbrev IsQuorum.spec : Prop :=
  ∀ (ql : GoSlice) (q : SetIds) (cl : GoSlice) (c : SetIds),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      setRO ql q ∗ setRO cl c ∗ ⌜q.length < 2 ^ 62⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsQuorum)) (Val #ql)) (Val #cl))
  {{ RET #(isQuorum q c); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
