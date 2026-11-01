/-
`watchableStoreTxnWrite.End` (`watchable_store_txn.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
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

/-- `tw.End()`: with no change, the inner transaction ended (no revision). With changes, the
events of the pending revision (`evsOfRevM`: a delete's key-value gets `ModRevision = rev`;
the key-values are shared with the watchers for good), then under `s.mu` the watchers
notified of them (`notify`, the revision sealed first so that their responses carry the log
that commits it) and the inner transaction ended (the revision committed): the notified log
is the committed one again. The sole writer is back at the committed log, with the reader
slots and the certificate. The inner `End`'s `Unlock` takes the batch lock's invariant `P` (the
store's, `hookIs`) back. -/
abbrev mvcc.watchableStoreTxnWrite.End.spec : Prop :=
  ∀ (trace : Loc) (tw s st : Loc) (γ : mvcc.WsNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (P : IProp GF) (f : val) (crev : Int) (ld : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchTxnWrite tw s st γ trace ilog pend puts deletes putSize crev ld ∗ mvcc.hookIs γ.st P f ∗ P ∗
      mvcc.certOkNext γ.st ilog pend }}
    (App (Val (tw @!! go.GoType.PointerType watchableStoreTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader st γ.st ∗ mvcc.idxCert γ.st.idx (mvcc.commitLog ilog pend) ∗
      mvcc.watchWriter γ (mvcc.commitLog ilog pend) ∗ (∃ te : Bool, traceutil.ownTrace trace te) ∗
      mvcc.writerFrag γ.st }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `tw.End()` ends the watchable store's write transaction begun at `σ`: its pending
changes committed by the caller's update, as `metricsTxnWrite.End.specC`, and sent to the
watchers before the revision is bumped; so the caller announces the log after the commit
(`mvccAnn`, nothing for no change), of which the watchers' events may be until it is committed. -/
abbrev mvcc.watchableStoreTxnWrite.End.specC : Prop :=
  ∀ (tw mw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState)
    (pend : List mvcc.Change) (P : IProp GF) (f : GoFunc) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.mvccWatchTxnOf tw mw ∗ mvcc.mvccTxn mw γ trace (.write σ pend) ∗
      (⌜pend = []⌝ ∨ mvcc.mvccAnn γ σ.log.length (σ.log ++ [pend])) ∗
      mvcc.mvccHook γ P f ∗ P ∗
      AU <{ ∃∃ (σ' : mvcc.MvccState), mvcc.mvccState γ σ' }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ (σ'.commit pend), COMM Q }> }}
    (App (Val (tw @!! go.GoType.PointerType watchableStoreTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); threadTok ∗ (∃ te : Bool, traceutil.ownTrace trace te) ∗ Q }}

end spec

end EtcdGrove
end Perennial
