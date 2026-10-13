/-
`storeTxnWrite.delete` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `tw.delete(key)`: the pending revision gets a delete of `key`, present after the pending
changes (the index's `Tombstone` then returns `nil`); the key's lease, if any, is detached. -/
abbrev mvcc.storeTxnWrite.delete.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key : GoSlice) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ key ↦*□ k ∗
      ⌜(mvcc.findKey k (mvcc.applyChanges (W64 ilog.length) (mvcc.stateAfter ilog) pend)).isSome ∧
        pend.length + 1 < mvcc.putMax γ⌝ }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"delete")) (Val #key))
  {{ RET #(); mvcc.storeTxnWriteIs tw s γ ilog (pend ++ [.del k]) }}

end spec

end EtcdGrove
end Perennial
