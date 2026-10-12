/-
`treeIndex.Insert` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex

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

/-- `ti.Insert(ki)` by the writer, with an owned key index `ki` of key `k` holding what the
writer's log gives `k` (not empty: the index has the key): `ReplaceOrInsert` replaces the key's
index in the tree, which is returned, owned; the writer's log is unchanged. (The insertion of a
new key, which `restore` does on its private index, is not a step of the live index: its
history fixes the tree's keys.) -/
abbrev mvcc.treeIndex.Insert.spec : Prop :=
  ∀ (ti : Loc) (γ : mvcc.IdxNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (ki : Loc)
    (k : GoString) (gs : GoSlice) (m : mvcc.KeyIndex),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTreeIndex ti γ ∗ mvcc.idxWriter γ ilog pend ∗ ⌜ki ≠ null⌝ ∗ mvcc.kiKey ki k ∗
      mvcc.ownKi ki gs m (DFrac.own 1) ∗
      ⌜m = mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k ∧ m ≠ mvcc.kiEmpty⌝ }}
    (App (Val (ti @!! go.GoType.PointerType treeIndex.ty @!! go!"Insert")) (Val #ki))
  {{ RET #(); mvcc.idxWriter γ ilog pend ∗
      ∃ (old : Loc) (gs' : GoSlice), ⌜old ≠ null⌝ ∗ mvcc.kiKey old k ∗
        mvcc.ownKi old gs' m (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial

