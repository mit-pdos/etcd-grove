/-
`newTreeIndex(lg)` (`index.go:45`): a `*treeIndex` over a fresh B-tree of degree 32 ordered by
`keyIndex.Less` (1g's `BTree.New`), as the `index` interface value, private to its maker until
published (`idxShareC`). A non-`nil` logger (`Compact` logs through it). Internal (`NewStore`,
`Restore`). **Changes**: over `ownIdxPriv`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `newTreeIndex(lg)`. -/
def newTreeIndex.spec : Prop :=
  ∀ (lg : Loc),
  {{ pkgInit ∗ ⌜lg ≠ null⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex)) (Val #lg))
  {{ (ti : Loc), RET #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti);
      ownIdxPriv ti (fun _ => none) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
