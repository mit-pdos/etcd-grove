/-
`metricsTxnWrite__Range` (metrics_txn.go / kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

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

/-- `tw.Range(ctx, key, end, ro)` of a transaction (a read or a write one, `TxnKind`, as `End`):
the wrapped transaction's range, counted: a read transaction's (`storeTxnCommon.Range`) at its
log and revision, a write transaction's (`storeTxnWrite.Range`) at its log with the pending
revision appended, at `writeRev` (`TxnKind.readLog`, `readRev`). At `context.TODO()` (`todo`), no
context error. (The read case, at an `isContext`, is the spec before the txn package's unit 1.) -/
abbrev mvcc.metricsTxnWrite.Range.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxn mw s γ kind ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isTxn mw s γ kind ∗
      mvcc.rangeOutcome r err kind.readLog kind.readRev (decide (endk = slice.nil)) k e ro }}

end spec

end EtcdGrove
end Perennial
