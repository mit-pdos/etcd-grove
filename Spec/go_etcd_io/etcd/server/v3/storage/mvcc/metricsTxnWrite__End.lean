/-
`metricsTxnWrite.End` (metrics_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
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

/-- `tw.End()` of a transaction (a read or a write one, `TxnKind`; a write one without its
key-values, `isTxnEnd`: `isTxn_toEnd`): the metrics updated, the wrapped transaction ended
(`storeTxnRead.End` or `storeTxnWrite.End`): the tokens are back, and a write transaction's
committed log is certified (`txnEndPost`). A write transaction's `Unlock` takes the batch
lock's invariant back (`txnEndPre`). At any compaction revision `crev`, the tokens back as
`storeReaderC` with the reader's tag `Z` (2026-10-13, unit 6a); the readers' statement
(`storeReader`) is `specR` (`spec_R`, `ReaderSpecs.lean`). -/
abbrev mvcc.metricsTxnWrite.End.spec : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isTxnEnd mw s γ trace kind crev Z ∗
      mvcc.txnEndPre γ kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.txnEndPost γ kind ∗
      (∃ te : Bool, traceutil.ownTrace trace te) }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.End()` ends a read transaction; the caller's thread token and trace are its own
again. (A write transaction of the watchable store ends by `watchableStoreTxnWrite.End`, which
notifies the watchers; this `End` would commit without notifying, and has no write spec.) -/
abbrev mvcc.metricsTxnWrite.End.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn mw γ trace (.read σ) }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); threadTok ∗ (∃ te : Bool, traceutil.ownTrace trace te) }}

end spec

end EtcdGrove
end Perennial
