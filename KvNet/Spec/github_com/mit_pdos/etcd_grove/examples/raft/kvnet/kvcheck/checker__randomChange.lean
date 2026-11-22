/-
`c.randomChange(cs)` (kvcheck.go): a random configuration change, as kvdurable's (its ids from
`changeID(cs)`): owned, its transition defined for its changes (`ccTransOk`), and at most three changes
(what bounds `PutConfChange`'s bytes, `encCC_length`).
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
abbrev checker.randomChange.spec : Prop :=
  ∀ (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) (csp : Loc) (cs : ConfStateM), 0 < ls.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗ isChecker c γ ls ∗ csOpt csp DFrac.discard cs }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty @!! go!"randomChange")) (Val #csp))
  {{ (cc : GoInterface) (o : ConfChangeIM), RET #cc;
      ownConfChangeI cc (DFrac.own 1) (some o) ∗
        ⌜ccTransOk o ∧ (ccToV2 o).changes.length ≤ 3⌝ }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
