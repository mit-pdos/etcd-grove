/-
`(*treeIndex).Insert(ki)` (`index.go:262`) on a private tree index, of an owned key index of a key
it does not have (1g's `ReplaceOrInsert` inserts it). Internal (`restoreIntoIndex`). **Changes**:
over `ownIdxPriv`.
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

/-- `ti.Insert(ki)` on a private index. -/
def treeIndex.Insert.spec : Prop :=
  ∀ (ti : Loc) P (kp : Loc) (k : GoString) (m : KeyIndexM),
  {{ pkgInit ∗ ownIdxPriv ti P ∗ ⌜P k = none⌝ ∗ ownKi kp k m (DFrac.own 1) }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Insert")) (Val #kp))
  {{ RET #(); ownIdxPriv ti (fun k' => if k' = k then some (kp, m) else P k') }}

end spec
end Mvcc
end EtcdGrove
end Perennial
