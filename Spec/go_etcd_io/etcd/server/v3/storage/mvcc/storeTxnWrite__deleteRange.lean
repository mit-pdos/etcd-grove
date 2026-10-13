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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tw.deleteRange(key, end)`: the keys of `[key, end)` (the one `key` if `end == nil`) with a
revision at the transaction's revision (`writeRev`: the pending one if it has a change, else
the committed log's last), `delKeys`, in key order, each deleted; their number. -/
abbrev mvcc.storeTxnWrite.deleteRange.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (key endk : GoSlice) (k e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      ⌜pend.length + (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length < mvcc.putMax γ⌝ }}
    (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"deleteRange"))
      (Val #key)) (Val #endk))
  {{ RET #(W64 ((mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length : Int) : w64);
      mvcc.storeTxnWriteIs tw s γ ilog
        (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del) }}

end spec

end EtcdGrove
end Perennial
