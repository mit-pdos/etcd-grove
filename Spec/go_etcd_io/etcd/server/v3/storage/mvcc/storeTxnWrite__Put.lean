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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.Put(key, value, lease)`: `put`, returning the pending revision. (Item 7b, 2026-11-17) In the owner's
lessor window `w`, as `put`. -/
abbrev mvcc.storeTxnWrite.Put.spec : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key value : GoSlice) (k v : GoString) (leaseID : w64) (L : List w64) (te : Bool) (crev : Int)
    (Z : IProp GF) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev Z ∗ key ↦*□ k ∗ value ↦*□ v ∗
      ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
      lease.leaseOwnW γ.leases L (mvcc.pendItems ilog pend) w ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ ∗
      traceutil.ownTrace trace te ∗
      ⌜lease.winMove w (mvcc.pendItems ilog pend) (mvcc.pendItems ilog (pend ++ [.put k v leaseID]))⌝ }}
    (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ RET #(W64 (ilog.length : Int) : w64);
      mvcc.storeTxnWriteIs tw s γ trace ilog (pend ++ [.put k v leaseID]) crev Z ∗
      lease.leaseOwnW γ.leases L (mvcc.pendItems ilog (pend ++ [.put k v leaseID])) w ∗
      traceutil.ownTrace trace te }}

end spec

end EtcdGrove
end Perennial
