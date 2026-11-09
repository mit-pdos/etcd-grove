/-
`newMetricsTxnWrite(tw)` (`metrics_txn.go:35`): `&metricsTxnWrite{tw, 0, 0, 0, 0}`. Internal
(`store.Write`). Mirrors its code.

**Changes**: unchanged from `specs-ref`'s file.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalTxn

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

/-- A fresh wrapper around `tw`. -/
def newMetricsTxnWrite.spec : Prop :=
  ∀ (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnWrite)) (Val #v))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      mw ↦ (go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite.mk v (W64 0) (W64 0) (W64 0) (W64 0)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
