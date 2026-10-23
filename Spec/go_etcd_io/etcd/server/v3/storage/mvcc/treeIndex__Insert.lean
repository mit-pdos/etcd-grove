/-
`treeIndex.Insert` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `ti.Insert(ki)` on a tree index no one else can reach (`ownIdxPriv`: its only caller,
`restoreIntoIndex`'s goroutine, rebuilds a private index; `notes/restore-plan.md`, R3), with an
owned key index `ki` of a key `k` the tree does not have: `ReplaceOrInsert` inserts it at its
place (`btInsert`). -/
abbrev mvcc.treeIndex.Insert.spec : Prop :=
  ∀ (ti : Loc) (L : List mvcc.IdxEntry) (ki : Loc) (k : GoString) (gs : GoSlice)
    (m : mvcc.KeyIndex),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownIdxPriv ti L ∗ ⌜ki ≠ null⌝ ∗ mvcc.kiKey ki k ∗ mvcc.ownKi ki gs m (DFrac.own 1) ∗
      ⌜∀ z ∈ L, z.2.1 ≠ k⌝ }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Insert")) (Val #ki))
  {{ RET #(); mvcc.ownIdxPriv ti (btInsert mvcc.entryLess (ki, k, m) L) }}

end spec

end EtcdGrove
end Perennial

