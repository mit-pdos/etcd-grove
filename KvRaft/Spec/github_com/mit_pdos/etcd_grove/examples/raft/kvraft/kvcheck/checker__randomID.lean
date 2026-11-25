/-
`c.randomID()` (kvcheck.go): a random replica's id, `1 + below(len(c.addrs))`: between `1` and
the number of replicas (of which there is at least one).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.randomID.spec : Prop :=
  ∀ (c : Loc) (γ : CheckerCnt GF) (ls : List GoString), 0 < ls.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗ isChecker c γ ls }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker.ty @!! go!"randomID")) (Val #()))
  {{ (id : w64), RET #id; ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ ls.length⌝ }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
