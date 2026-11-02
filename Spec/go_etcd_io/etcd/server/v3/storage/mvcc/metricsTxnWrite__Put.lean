/-
`metricsTxnWrite.Put` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.Put(key, value, lease)` of a write transaction: the counters, then the wrapped `Put`. -/
abbrev mvcc.metricsTxnWrite.Put.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (key value : GoSlice) (k v : GoString) (leaseID : w64) (L : List w64)
    (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z ∗ key ↦*□ k ∗ value ↦*□ v ∗
      ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
      lease.leaseOwn γ.leases L (mvcc.pendItems ilog pend) ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ }}
    (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ RET #(W64 (ilog.length : Int) : w64);
      mvcc.isTxnWrite mw s γ trace ilog (pend ++ [.put k v leaseID]) (puts + W64 1) deletes
        (putSize + (key.len + value.len)) crev Z ∗
      lease.leaseOwn γ.leases L (mvcc.pendItems ilog (pend ++ [.put k v leaseID])) }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.Put(key, value, lease)` in a write transaction begun at `σ`: the put appended to the
pending changes, at the pending revision (returned); the lease (none, or a live one) attached in
the lessor's item map, which the caller, the lease owner, holds at the pending state's. With a
lease, the key is shorter than `2 ^ 63 - 1` (the premise of the real lessor's `Attach` in
`isLessor`, which its proof needs, invariant `itemKeysShort`; the Go code needs no key bound). -/
abbrev mvcc.metricsTxnWrite.Put.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState) (pend : List mvcc.Change)
    (key value : GoSlice) (k v : GoString) (leaseID : w64) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace (.write σ pend) ∗ key ↦*□ k ∗ value ↦*□ v ∗
      ⌜leaseID ≠ W64 0 → (k.length : Int) < 2 ^ 63 - 1⌝ ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L (mvcc.pendItems σ.log pend) ∗
      ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ }}
    (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ RET #(W64 (σ.log.length : Int) : w64);
      mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace (.write σ (pend ++ [.put k v leaseID])) ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L (mvcc.pendItems σ.log (pend ++ [.put k v leaseID])) }}

end spec

end EtcdGrove
end Perennial
