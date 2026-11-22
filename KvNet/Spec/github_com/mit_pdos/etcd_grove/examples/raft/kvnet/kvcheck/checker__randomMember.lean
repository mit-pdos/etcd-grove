/-
`c.randomMember()` (kvcheck.go): a random member of the configuration last recorded (`lastConf`,
read under `mu`, `checkerInv`), or a random replica: a replica's id, `1 ≤ id ≤ len(c.addrs)`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Defs

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.randomMember.spec : Prop :=
  ∀ (c : Loc) (γ : CheckerCnt GF) (ls : List GoString), 0 < ls.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗ isChecker c γ ls }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty @!! go!"randomMember")) (Val #()))
  {{ (id : w64), RET #id; ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ ls.length⌝ }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
