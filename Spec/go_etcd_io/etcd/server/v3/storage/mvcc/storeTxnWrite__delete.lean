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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.delete(key)`: the pending revision gets a delete of `key`, present after the pending
changes (the index's `Tombstone` then returns `nil`); the key's lease, if any, is detached. (Item 7b, 2026-11-17)
In the owner's lessor window `w`, the delete moves the key's item toward the target (`winMove`). -/
abbrev mvcc.storeTxnWrite.delete.spec : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key : GoSlice) (k : GoString) (L : List w64) (crev : Int) (Z : IProp GF) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev Z ∗ key ↦*□ k ∗
      lease.leaseOwnW γ.leases L (mvcc.pendItems ilog pend) w ∗
      ⌜(mvcc.findKey k (mvcc.applyChanges (W64 ilog.length) (mvcc.stateAfter ilog) pend)).isSome⌝ ∗
      ⌜lease.winMove w (mvcc.pendItems ilog pend) (mvcc.pendItems ilog (pend ++ [.del k]))⌝ }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"delete")) (Val #key))
  {{ RET #(); mvcc.storeTxnWriteIs tw s γ trace ilog (pend ++ [.del k]) crev Z ∗
      lease.leaseOwnW γ.leases L (mvcc.pendItems ilog (pend ++ [.del k])) w }}

end spec

end EtcdGrove
end Perennial
