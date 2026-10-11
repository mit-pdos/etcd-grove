/-
`newMetricsTxnWrite` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `newMetricsTxnWrite(tw)`: a fresh `metricsTxnWrite` around `tw`, its counters zero. -/
abbrev mvcc.newMetricsTxnWrite.spec : Prop :=
  ∀ (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnWrite)) (Val #v))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      mw ↦ ({
        TxnWrite' := v, ranges' := W64 0, puts' := W64 0, deletes' := W64 0,
        putSize' := W64 0 } : metricsTxnWrite) }}

end spec

end EtcdGrove
end Perennial
