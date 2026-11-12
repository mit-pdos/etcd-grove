/-
`newMetricsTxnRead(tr)` (`metrics_txn.go:31`): `&metricsTxnWrite{&txnReadWrite{tr}, 0, 0, 0, 0}`.
Internal (`store.Read`). Mirrors its code.

**Changes**: unchanged from `specs-ref`'s file.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- Two fresh wrappers around `tr`. -/
def newMetricsTxnRead.spec : Prop :=
  ∀ (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnRead)) (Val #v))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      ∃ trw : Loc,
        mw ↦ (go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite.mk
          (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) (W64 0) (W64 0) (W64 0) (W64 0)) ∗
        trw ↦ ({ TxnRead' := v } : go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
