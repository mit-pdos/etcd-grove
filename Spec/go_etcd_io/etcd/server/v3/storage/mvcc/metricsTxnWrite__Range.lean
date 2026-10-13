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
context error. (The read case, at an `isContext`, is the spec before the txn package's unit 1.)
At the compaction revision `crev` the transaction observed (`rangeOutcomeC`; 2026-10-13, unit
6a); the frozen statement (`crev = -1`: `rangeOutcome`) is `specFrozen` (`spec_frozen`). -/
abbrev mvcc.metricsTxnWrite.Range.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxn mw s γ kind crev Z ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isTxn mw s γ kind crev Z ∗
      mvcc.rangeOutcomeC r err kind.readLog kind.readRev crev (decide (endk = slice.nil)) k e ro }}

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.metricsTxnWrite.Range.specFrozen : Prop :=
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

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.metricsTxnWrite.Range.spec_frozen
    (h : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.specFrozen (GF := GF) (hG := hG) := by
  intro mw s γ kind ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, Htx, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply (h mw s γ kind ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ)) $$ %Φ [Htx]
  · iframe Htx; iframe #
  inext
  iintro %r %err ⟨%Ht, Htx, Hout⟩
  icases mvcc.isTxn_readRev mw s γ kind (-1) (mvcc.crevFrozen γ) $$ Htx with ⟨Htx, %Hrv⟩
  iapply HΦ
  iframe Htx
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv $$ Hout

end spec

end EtcdGrove
end Perennial
