/-
`(*treeIndex).Put(key, rev)` (`index.go:54`): under the tree lock, the key's key index gets the
revision (a fresh one inserted if none: 1g's `Get`, `ReplaceOrInsert`), by the caller's update
(`idxPut`); the revision above the key's last (`keyIndex.put` panics otherwise). The key's bytes kept.
Internal (`storeTxnWrite.put`). **Changes** from `specs-ref`'s file: an atomic update over
`idxAt` (the store's invariant holds it) for the writer's log fragment.
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

/-- `ti.Put(key, rev)`. -/
def treeIndex.Put.spec : Prop :=
  ∀ (ti : Loc) (γi : IdxName) (key : GoSlice) (k : GoString) (rev : Revision) (Q : IProp GF),
  {{ pkgInit ∗ isTreeIndex (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti) γi ∗
      key ↦*□ k ∗
      AU <{ ∃∃ (M : IndexM) (c : Int), idxAt γi M c ∗
              ⌜∀ ki, M k = some ki → Rev.gt (revOf rev) ki.modified = true⌝ }> @ ⊤ \ ↑idxN, ∅
        <{ idxAt γi (idxPut M k (revOf rev)) c, COMM Q }> }}
    (App (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Put")) (Val #key)) (Val #rev))
  {{ RET #(); Q }}

end spec
end Mvcc
end EtcdGrove
end Perennial
