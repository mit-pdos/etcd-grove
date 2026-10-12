/-
`metricsTxnWrite.Rev` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`, here a read
transaction's `txnReadWrite` around a `storeTxnRead`, down to `storeTxnCommon.Rev`). Lean-first
(no Rocq counterpart); see `InvStore.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `mw.Rev()` of a read transaction: the read transaction's revision, the last of its committed log. -/
abbrev mvcc.metricsTxnWrite.Rev.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnRead mw s γ log rev }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(rev : w64); mvcc.isTxnRead mw s γ log rev }}

end spec

end EtcdGrove
end Perennial
