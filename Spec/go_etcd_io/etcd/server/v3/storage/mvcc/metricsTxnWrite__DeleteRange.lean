/-
`metricsTxnWrite.DeleteRange` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.DeleteRange(key, end)` of a write transaction: the counter, then the wrapped
`DeleteRange`. -/
abbrev mvcc.metricsTxnWrite.DeleteRange.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (key endk : GoSlice) (k e : GoString) (L : List w64) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      lease.leaseOwn γ.leases L (mvcc.pendItems ilog pend) }}
    (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"DeleteRange"))
      (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev);
      mvcc.isTxnWrite mw s γ trace ilog
        (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del)
        puts (deletes + W64 1) putSize crev Z ∗
      lease.leaseOwn γ.leases L (mvcc.pendItems ilog (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del)) ∗
      ⌜n = W64 ((mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).length : Int) ∧
        rev = W64 ((mvcc.writeRev ilog
          (pend ++ (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e).map .del) : Nat) : Int)⌝ }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.DeleteRange(key, end)` in a write transaction begun at `σ`: the keys of the range
present in the pending state deleted, in key order (`delKeys`), appended to the pending changes,
and detached from their leases in the item map; their number and the pending revision (the
transaction's revision if nothing is pending) returned. -/
abbrev mvcc.metricsTxnWrite.DeleteRange.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState) (pend : List mvcc.Change)
    (key endk : GoSlice) (k e : GoString) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.mvccTxn mw γ trace (.write σ pend) ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L (mvcc.pendItems σ.log pend) }}
    (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"DeleteRange"))
      (Val #key)) (Val #endk))
  {{ (n rev : w64), RET (PairV #n #rev);
      mvcc.mvccTxn mw γ trace (.write σ (pend ++ (mvcc.delKeys σ.log pend (decide (endk = slice.nil)) k e).map .del)) ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L (mvcc.pendItems σ.log (pend ++ (mvcc.delKeys σ.log pend (decide (endk = slice.nil)) k e).map .del)) ∗
      ⌜n = W64 ((mvcc.delKeys σ.log pend (decide (endk = slice.nil)) k e).length : Int) ∧
        rev = W64 ((mvcc.writeRev σ.log (pend ++ (mvcc.delKeys σ.log pend (decide (endk = slice.nil)) k e).map .del) : Nat) : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
