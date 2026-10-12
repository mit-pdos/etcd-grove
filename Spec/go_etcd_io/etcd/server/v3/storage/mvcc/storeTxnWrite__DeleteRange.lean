/-
`storeTxnWrite.DeleteRange` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.DeleteRange(key, end)`: `deleteRange`, returning the number of keys deleted and the
transaction's revision after it (the pending one once it has a change, else the committed
log's last). -/
abbrev mvcc.storeTxnWrite.DeleteRange.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key endk : GoSlice) (k e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      ⌜pend.length + (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length < 2 ^ 63⌝ }}
    (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"DeleteRange"))
      (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev);
      mvcc.storeTxnWriteIs tw s γ ilog
        (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del) ∗
      ⌜n = W64 ((mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length : Int) ∧
        rev = W64 ((mvcc.writeRev ilog
          (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del) : Nat) : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
