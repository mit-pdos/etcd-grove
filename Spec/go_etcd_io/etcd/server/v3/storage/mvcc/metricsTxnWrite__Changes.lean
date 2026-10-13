/-
`metricsTxnWrite.Changes` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`, here a write
transaction's `storeTxnWrite.Changes`). Lean-first (no Rocq counterpart); added for the server's
txn package (unit 3: `txn` and `executeTxn` test `len(txnWrite.Changes())`); see `InvStore.lean`.
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

/-- `mw.Changes()` of a write transaction: its `changes` slice, the key-values of its pending
changes (`changesAre`), one per pending change, the caller's (the watchable store's `End`
shares them with the watchers); the transaction keeps its core (`isTxnWrite_join` gives the
transaction back). -/
abbrev mvcc.metricsTxnWrite.Changes.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize crev Z }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Changes")) (Val #()))
  {{ (chs : GoSlice) (ps : List Loc), RET #chs;
      chs ↦* ps ∗ mvcc.changesAre ps ilog pend ∗ ⌜ps.length = pend.length⌝ ∗
      mvcc.isTxnWriteCore mw s γ ilog pend puts deletes putSize chs ps false crev Z }}

end spec

end EtcdGrove
end Perennial
