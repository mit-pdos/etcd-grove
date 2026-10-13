/-
`storeTxnWrite.Put` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.Put(key, value, lease)`: `put`, returning the pending revision. -/
abbrev mvcc.storeTxnWrite.Put.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key value : GoSlice) (k v : GoString) (leaseID : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ key ↦*□ k ∗ value ↦*□ v ∗
      (⌜leaseID = W64 0⌝ ∨ mvcc.leaseKnown γ.leases leaseID) ∗ ⌜pend.length + 1 < mvcc.putMax γ⌝ }}
    (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ RET #(W64 (ilog.length : Int) : w64);
      mvcc.storeTxnWriteIs tw s γ ilog (pend ++ [.put k v leaseID]) }}

end spec

end EtcdGrove
end Perennial
