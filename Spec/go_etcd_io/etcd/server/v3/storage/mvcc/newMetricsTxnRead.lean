/-
`newMetricsTxnRead` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `newMetricsTxnRead(tr)` wraps `tr` in a `txnReadWrite` and that in a `metricsTxnWrite` with zero
counters, returned as a `TxnRead`. -/
abbrev mvcc.newMetricsTxnRead.spec : Prop :=
  ∀ (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnRead)) (Val #v))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      ∃ trw : Loc,
        mw ↦ ({
          TxnWrite' := interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw,
          ranges' := W64 0, puts' := W64 0, deletes' := W64 0, putSize' := W64 0 } : metricsTxnWrite) ∗
        trw ↦ ({ TxnRead' := v } : txnReadWrite) }}

end spec

end EtcdGrove
end Perennial
