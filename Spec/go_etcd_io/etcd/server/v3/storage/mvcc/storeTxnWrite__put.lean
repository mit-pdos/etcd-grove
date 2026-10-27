/-
`storeTxnWrite.put` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.put(key, value, leaseID)`: the pending revision gets a put of `key` (the index's
answer of the key at the pending revision gives the create revision and version, the
lessor's `GetLease` the old lease to detach, and `leaseID` is attached). The key's and
value's bytes are read-only for good (the index and the change keep them); the lease, if
any, is a granted one; the revision has room for the change. (Unit T3, L2b, 2026-10-25) The
lease owner's item map is the pending state's (`pendItems`), before and after: `GetLease` finds
the key's old lease in it, `Detach` and `Attach` move the key. -/
abbrev mvcc.storeTxnWrite.put.spec : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key value : GoSlice) (k v : GoString) (leaseID : w64) (L : List w64) (te : Bool) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev Z ∗ key ↦*□ k ∗ value ↦*□ v ∗
      lease.leaseOwn γ.leases L (mvcc.pendItems ilog pend) ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ ∗
      traceutil.ownTrace trace te }}
    (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"put")) (Val #key))
      (Val #value)) (Val #leaseID))
  {{ RET #(); mvcc.storeTxnWriteIs tw s γ trace ilog (pend ++ [.put k v leaseID]) crev Z ∗
      lease.leaseOwn γ.leases L (mvcc.pendItems ilog (pend ++ [.put k v leaseID])) ∗
      traceutil.ownTrace trace te }}

end spec

end EtcdGrove
end Perennial
