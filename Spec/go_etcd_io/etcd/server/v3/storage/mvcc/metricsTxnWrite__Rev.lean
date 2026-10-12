/-
`metricsTxnWrite.Rev` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`: a read
transaction's `txnReadWrite` around a `storeTxnRead`, down to `storeTxnCommon.Rev`, or a write
transaction's `storeTxnWrite.Rev`). Lean-first
(no Rocq counterpart); see `InvStore.lean`.
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

/-- `mw.Rev()` of a transaction of either kind: the revision it began at (`TxnKind.beginRev`: a
read transaction's revision, a write transaction's committed log's last). -/
abbrev mvcc.metricsTxnWrite.Rev.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxn mw s γ kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(kind.beginRev : w64); mvcc.isTxn mw s γ kind }}

end spec

end EtcdGrove
end Perennial
