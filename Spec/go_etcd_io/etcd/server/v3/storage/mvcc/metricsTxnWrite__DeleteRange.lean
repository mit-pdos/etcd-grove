/-
`metricsTxnWrite.DeleteRange` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.DeleteRange(key, end)` of a write transaction: the counter, then the wrapped
`DeleteRange`. -/
abbrev mvcc.metricsTxnWrite.DeleteRange.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (key endk : GoSlice) (k e : GoString) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize crev Z ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      ⌜pend.length + (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length < mvcc.putMax γ⌝ }}
    (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"DeleteRange"))
      (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev);
      mvcc.isTxnWrite mw s γ ilog
        (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del)
        puts (deletes + W64 1) putSize crev Z ∗
      ⌜n = W64 ((mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length : Int) ∧
        rev = W64 ((mvcc.writeRev ilog
          (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del) : Nat) : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
