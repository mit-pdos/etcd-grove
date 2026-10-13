/-
`metricsTxnWrite.FirstRev` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`, here a read
transaction's `txnReadWrite` around a `storeTxnRead`, down to `storeTxnCommon.FirstRev`). Lean-first
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

/-- `mw.FirstRev()` of a read transaction: the compaction revision `crev` it observed (`store.Read`
sets `firstRev` from `s.compactMainRev`; 2026-10-13, unit 6a: `-1` of the frozen transaction, the
instance at `isTxnRead`'s defaults). -/
abbrev mvcc.metricsTxnWrite.FirstRev.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnRead mw s γ log rev crev Z }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"FirstRev")) (Val #()))
  {{ RET #(W64 crev : w64); mvcc.isTxnRead mw s γ log rev crev Z }}

end spec

end EtcdGrove
end Perennial
