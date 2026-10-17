/-
`watchableStore.syncWatcherCohort` (`watchable_store.go`, etcd-io/etcd#22304). Lean-first (no
Rocq counterpart); see `InvWatchSync.lean`, `Cohorts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `s.syncWatcherCohort(wg, minRev, maxScanRev, curRev, compactionRev)`, called by
`syncWatchers` under `s.mu` and `s.store.revMu` (read), with the lock's state `σ` (its body,
`watchStoreBody`), the committed log `C` (`curRev = len(C) - 1`; `compactionRev = -1`: the
watchable store's inner store is never compacted, `crevFrozen`), and the read side's parts the
scan needs (the backend's read token `storeRT`, the bucket's view of `C`, the index's log). The
cohort `wg` holds unsynced watchers `Wc`, each at or above `minRev` and below `maxScanRev`
(`maxScanRev ≤ len(C)`).

It scans `[minRev, maxScanRev)` (`rangeEvents`) and hands each member its events from its own
`minRev`: a member with none becomes synced if the scan reached the current revision
(`maxScanRev = len(C)`), else stays unsynced at `maxScanRev`; one with events gets them in one
response (all of them, or under the cap of `watchBatchMaxRevs` revisions those below the first
revision left out), and becomes synced if the scan reached the current revision and nothing was
left out, stays unsynced at `maxScanRev` or at the first revision left out otherwise, or becomes a
victim with its batch if its channel is full. The lock's state after (`σ'`) keeps the lock
invariant (`watchStoreBody`: every delivery recorded) and differs from `σ` only at the cohort's
members (the unsynced group shrinks). -/
abbrev mvcc.watchableStore.syncWatcherCohort.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (σ : mvcc.WsState) (C : mvcc.Log) (wg : Loc)
    (Wc : GMap Loc mvcc.WatchRange) (minRev maxScanRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.storeRT γ.st ∗ mvcc.crevFrozen γ.st ∗
      mvcc.bucketView γ.st sync.rfrac.half (mvcc.bucketMap C) ∗
      mvcc.idxCert γ.st.idx C ∗ mvcc.certOk γ.st C ∗
      mvcc.idxLogAuth γ.st.idx (mvcc.revQ γ.st sync.rfrac) C ∗
      mvcc.watchStoreBody s γ 1 σ ∗ mvcc.ownWatcherGroup wg Wc ∗
      ⌜C ≠ [] ∧ C.length < 2 ^ 63 ∧
        0 ≤ sint.Z minRev ∧ sint.Z minRev ≤ sint.Z maxScanRev ∧ sint.Z maxScanRev ≤ C.length ∧
        (∃ w, (Wc !! w).isSome) ∧
        (∀ w r, Wc !! w = some r → σ.Wu !! w = some r) ∧
        (∀ w st, (Wc !! w).isSome → σ.ST !! w = some st →
          sint.Z minRev ≤ sint.Z st.minRev ∧ sint.Z st.minRev < sint.Z maxScanRev)⌝ }}
    (App (App (App (App (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!!
        go!"syncWatcherCohort")) (Val #wg)) (Val #minRev)) (Val #maxScanRev))
        (Val #(W64 ((C.length : Int) - 1)))) (Val #(W64 (-1))))
  {{ RET #(); ∃ σ' : mvcc.WsState,
      mvcc.storeRT γ.st ∗ mvcc.bucketView γ.st sync.rfrac.half (mvcc.bucketMap C) ∗
      mvcc.idxLogAuth γ.st.idx (mvcc.revQ γ.st sync.rfrac) C ∗
      mvcc.watchStoreBody s γ 1 σ' ∗
      ⌜(∀ w r, σ'.Wu !! w = some r → σ.Wu !! w = some r) ∧
        ∀ w, Wc !! w = none → σ'.Wu !! w = σ.Wu !! w ∧ σ'.ST !! w = σ.ST !! w⌝ }}

end spec

end EtcdGrove
end Perennial
