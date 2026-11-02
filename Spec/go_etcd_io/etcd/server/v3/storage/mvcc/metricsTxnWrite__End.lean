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

/-- **`End` in either mode, with the caller's commit update** (mvcc's candidate API,
`notes/mvcc-api-proof-plan.md`, stage P2): `spec`'s, over `txnEndPreA`/`txnEndPostA`
(`storeTxnWrite.End.specA`'s). -/
abbrev mvcc.metricsTxnWrite.End.specA : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (crev : Int)
    (Z : IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isTxnEnd mw s γ trace kind crev Z ∗
      mvcc.txnEndPreA γ Q kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC s γ ∗ □ Z ∗ mvcc.txnEndPostA γ Q kind ∗
      (∃ te : Bool, traceutil.ownTrace trace te) }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.End()` ends a transaction: a read one; or a write one begun at `σ`, its pending changes
committed (none: no revision) by the caller's updates (the commit's two steps, both at the bump:
this `End` notifies no watcher), the batch lock's invariant `P` given back, once its watchers were
taken care of (`mvccWatchersOk`: free for a store without watchers or a commit of nothing; for a
watched store only the watchable store's `End`, which notifies, has it). The caller's thread token
and trace are its own again. -/
abbrev mvcc.metricsTxnWrite.End.specC : Prop :=
  ∀ (mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (k : mvcc.MTxn) (P : IProp GF) (f : GoFunc)
    (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) γ trace k ∗
      match k with
      | .read _ => iprop(True)
      | .write σ₀ pend => iprop(mvcc.mvccWatchersOk γ (.commit σ₀ pend) ∗ mvcc.mvccHook γ P f ∗ P ∗
          AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ }> @ ⊤ \ ↑mvcc.mvccN, ∅
            <{ mvcc.mvccState γ (σ.notify pend), COMM
                AU <{ ∃∃ (σ' : mvcc.MvccState), mvcc.mvccState γ σ' }> @ ⊤ \ ↑mvcc.mvccN, ∅
                  <{ mvcc.mvccState γ σ'.commitPending, COMM Q }> }>) }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); threadTok ∗ (∃ te : Bool, traceutil.ownTrace trace te) ∗
      match k with
      | .read _ => iprop(True)
      | .write _ _ => Q }}

end spec

end EtcdGrove
end Perennial
