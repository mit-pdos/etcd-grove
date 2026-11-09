/-
`(*storeTxnCommon).Range(ctx, key, end, ro)` (`kvstore_txn.go:69`): `rangeKeys` at the transaction's
`Rev()`. Internal: a read transaction's `Range` (promoted to `storeTxnRead`; `storeTxnWrite` has its
own). Proof sketch: `Rev.spec`, then `rangeKeys.spec` at `rev = σ.rev = (.read σ).readHist.rev`.

**Changes** from `specs-ref`'s file: over `txnCommon` and `rangeOut` (W0's history).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A read transaction's range: its outcome over the transaction's state. -/
def storeTxnCommon.Range.spec : Prop :=
  ∀ (c : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (ctx : GoInterface) (key endk : GoSlice)
    (kk e : Bytes) (dk de : DFrac) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      txnCommon c γ trace (.read σ) ∗ traceOwn trace ∗ Context.ctxOk ctx ∗ key ↦*{dk} kk ∗ endk ↦*{de} e }}
    (App (App (App (App (Val (c @!! go.GoType.PointerType storeTxnCommon.ty @!! go!"Range"))
      (Val #ctx)) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      txnCommon c γ trace (.read σ) ∗ traceOwn trace ∗ key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      ∃ out : RangeOut, ⌜rangeOut σ.kv σ.crev (mrange kk endk e) ro out⌝ ∗ rangeResOwn ctx r err out }}

end spec
end Mvcc
end EtcdGrove
end Perennial
