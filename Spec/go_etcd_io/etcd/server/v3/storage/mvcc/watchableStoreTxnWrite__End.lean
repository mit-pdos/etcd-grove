/-
`watchableStoreTxnWrite.End` (`watchable_store_txn.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WsTxnSteps

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
store's, `hookIs`) back. (M4, track B, 2026-11-06; `Api/TxnSteps.lean`) The API's ghost state
moves by the caller's step (`wsEndCb`): with a change, its notification under `s.mu` (with the
lock's slot) before the watchers are sent the revision's events, then the commit's step at the
inner `End`'s bump; with none, the commit's step; the frozen state excluded by the caller's `G`
(given back). (M4, track B, 2026-11-06, the watchable write transaction of the API) The transaction's
trace part any `Tr` (`isWatchTxnWriteT`, given back: the API's transaction holds none); the batch
lock's invariant by the store's name of it alone (`hookP`, as the plain `End`), no writer's
fragment back, the reader back as `storeReaderC`; and the step at the writer slot's compaction
revision (`wsEndCbY`: `slotYc`, the transaction's), so that the API's step can tell the state it
fires at is the one the transaction began at. -/
abbrev mvcc.watchableStoreTxnWrite.End.spec : Prop :=
  ∀ (trace : Loc) (tw s st : Loc) (γ : mvcc.WsNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (puts deletes putSize : w64) (P : IProp GF) (crev : Int) (ld : Bool) (G R Tr : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchTxnWriteT tw s st γ trace ilog pend puts deletes putSize crev ld Tr ∗
      mvcc.hookP γ.st P ∗ P ∗ mvcc.certOkNext γ.st ilog pend ∗
      G ∗ □ (mvcc.slotF γ.st ∗ G -∗ False) ∗ mvcc.wsEndCbY γ ilog pend crev R }}
    (App (Val (tw @!! go.GoType.PointerType watchableStoreTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC st γ.st ∗ mvcc.idxCert γ.st.idx (mvcc.commitLog ilog pend) ∗
      mvcc.watchWriter γ (mvcc.commitLog ilog pend) ∗ Tr ∗ G ∗ R }}

end spec

end EtcdGrove
end Perennial
