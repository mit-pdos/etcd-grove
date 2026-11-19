/-
`storeTxnWrite.deleteRange` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.deleteRange(key, end)`: the keys of `[key, end)` (the one `key` if `end == nil`) with a
revision at the transaction's revision (`writeRev`: the pending one if it has a change, else
the committed log's last), `delKeys`, in key order, each deleted; their number. (Item 7b, 2026-11-17)
In the owner's lessor window `w`, the deletes move their keys' items toward the target (`winMove`). -/
abbrev mvcc.storeTxnWrite.deleteRange.spec : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key endk : GoSlice) (k e : GoString) (L : List w64) (crev : Int) (Z : IProp GF) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev Z ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      lease.leaseOwnW γ.leases L (mvcc.pendItems ilog pend) w ∗
      ⌜lease.winMove w (mvcc.pendItems ilog pend) (mvcc.pendItems ilog (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del))⌝ ∗
      ⌜mvcc.LogPutsLe etcdKeyMax ilog ∧ mvcc.ChPutsLe etcdKeyMax pend⌝ }}
    (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"deleteRange"))
      (Val #key)) (Val #endk))
  {{ RET #(W64 ((mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length : Int) : w64);
      mvcc.storeTxnWriteIs tw s γ trace ilog
        (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del) crev Z ∗
      lease.leaseOwnW γ.leases L (mvcc.pendItems ilog (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del)) w }}

end spec

end EtcdGrove
end Perennial
