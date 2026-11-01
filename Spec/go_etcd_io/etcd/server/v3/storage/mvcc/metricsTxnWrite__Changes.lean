/-
`metricsTxnWrite.Changes` (`metrics_txn.go`: promoted from the wrapped `TxnWrite`, here a write
transaction's `storeTxnWrite.Changes`). Lean-first (no Rocq counterpart); added for the server's
txn package (unit 3: `txn` and `executeTxn` test `len(txnWrite.Changes())`); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `mw.Changes()` of a write transaction: its `changes` slice, the key-values of its pending
changes (`changesAre`), one per pending change, the caller's (the watchable store's `End`
shares them with the watchers); the transaction keeps its core (`isTxnWrite_join` gives the
transaction back). -/
abbrev mvcc.metricsTxnWrite.Changes.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) (ld : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z ld }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Changes")) (Val #()))
  {{ (chs : GoSlice) (ps : List Loc), RET #chs;
      chs ↦* ps ∗ mvcc.changesAre ps ilog pend ∗ ⌜ps.length = pend.length⌝ ∗
      mvcc.isTxnWriteCore mw s γ trace ilog pend puts deletes putSize chs ps false crev Z ld }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.Changes()`: the transaction's change records, one per pending change (none for a
read transaction). Only their number is stated: the watchable store's `End` writes them and hands
them to the watchers, and callers inspect the length. -/
abbrev mvcc.metricsTxnWrite.Changes.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (k : mvcc.MTxn),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn mw γ trace k }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Changes")) (Val #()))
  {{ (chs : GoSlice), RET #chs; mvcc.mvccTxn mw γ trace k ∗ ⌜uint.nat chs.len = k.pend.length⌝ }}

end spec

end EtcdGrove
end Perennial
