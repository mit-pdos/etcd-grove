/-
`metricsTxnWrite.Put` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.Put(key, value, lease)` of a write transaction: the counters, then the wrapped `Put`. -/
abbrev mvcc.metricsTxnWrite.Put.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (key value : GoSlice) (k v : GoString) (leaseID : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize ∗ key ↦*□ k ∗ value ↦*□ v ∗
      (⌜leaseID = W64 0⌝ ∨ mvcc.leaseKnown γ.leases leaseID) ∗ ⌜pend.length + 1 < 2 ^ 63⌝ }}
    (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ RET #(W64 (ilog.length : Int) : w64);
      mvcc.isTxnWrite mw s γ ilog (pend ++ [.put k v leaseID]) (puts + W64 1) deletes
        (putSize + (key.len + value.len)) }}

end spec

end EtcdGrove
end Perennial
