/-
`(*treeIndex).Tombstone(key, rev)` (`index.go:192`): under the tree lock, the key's key index
tombstoned (`idxTombstone`), by the caller's update; `ErrRevisionNotFound` for a key without one or
already deleted (nothing changes). The revision above the key's last (`put`'s panic otherwise).
Internal (`storeTxnWrite.delete`). **Changes**: an atomic update over `idxAt`.
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

/-- `ti.Tombstone(key, rev)`. -/
def treeIndex.Tombstone.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (key : GoSlice) (k : GoString) (dk : DFrac) (rev : Revision)
    (e : GoInterface) (Q : IndexM → IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      key ↦*{dk} k ∗ globalAddr ErrRevisionNotFound ↦□ e ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗
              ⌜∀ ki, M k = some ki → kiLastEmpty ki = false → Rev.gt (revOf rev) ki.modified = true⌝ }>
          @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi ((idxTombstone M k (revOf rev)).getD M) c, COMM Q M }> }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Tombstone")) (Val #key)) (Val #rev))
  {{ (err : GoInterface), RET #err; key ↦*{dk} k ∗ ∃ M : IndexM, Q M ∗
      ⌜err = (match idxTombstone M k (revOf rev) with | none => e | some _ => GoInterface.nil)⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
