/-
`(*storeTxnWrite).Range(ctx, key, end, ro)` (`kvstore_txn.go:189`): `rangeKeys` at `beginRev`, or
`beginRev + 1` once the transaction has a change (`= (.write σ pend).readHist.rev`). Internal
(`Txn.Range.contract` through `metricsTxnWrite`, 3f's `watchableStoreTxnWrite`). Proof sketch:
`storeTxnW_common`, `rangeKeys.spec`.

**Changes** from `specs-ref`'s file: over `storeTxnW` and `rangeOut` (W0's history).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

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

/-- A write transaction's range: over the history with its events committed. -/
def storeTxnWrite.Range.spec : Prop :=
  ∀ (t : Loc) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Event) (ctx : GoInterface)
    (key endk : GoSlice) (kk e : Bytes) (dk de : DFrac) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeTxnW t γ trace σ pend ∗ traceOwn trace ∗ Context.ctxOk ctx ∗ key ↦*{dk} kk ∗ endk ↦*{de} e }}
    (App (App (App (App (Val (t @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Range"))
      (Val #ctx)) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      storeTxnW t γ trace σ pend ∗ traceOwn trace ∗ key ↦*{dk} kk ∗ endk ↦*{de} e ∗
      ∃ out : RangeOut, ⌜rangeOut (MTxn.write σ pend).readHist σ.crev (mrange kk endk e) ro out⌝ ∗
        rangeResOwn ctx r err out }}

end spec
end Mvcc
end EtcdGrove
end Perennial
