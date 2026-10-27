/-
`store.Restore` (`kvstore.go`): proved (`notes/restore-plan.md`, R5f, 2026-10-24) over `restore`'s
spec and the ghost moves of `RestoreMoves.lean`. Lean-first (no Rocq counterpart); see
`InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- **`s.Restore(b')`: the store restored over a new backend `b'` holding the committed log `L'`,
which extends the store's committed log `L`** (D22 receiver epochs, S6, 2026-10-22; proved in the
restore plan's R5f, 2026-10-24), returning `nil`. The store's logical names `γ` stay (`isStore s γ`, the
committed log, the index's history, the revision budget, the certificates, the readers' tickets);
its physical ones move to fresh ones `γ' := γ.withPhys p'` (the new backend's bucket and instance
`d'`, a new index's event count and compactor, a new scheduler's, the new batch lock's invariant
`P'`, key and view log, the compaction's meta record and counter).

**Precondition.** The caller holds every part of the store's current objects and names
(`γ.cur`) not in a lock or an invariant `Restore` takes or opens: the right to close the store
(`storeCloser`: an eighth, the stop channel's close, the scheduler's stop token, the compaction
queue; with it no compaction right exists, so no compaction job runs and no part of `γ.cur` is
discarded, `compactRight_of_closer`), the watchable store's quarter of the fields with its deposit
ghost (`fieldShare … ¼ ∗ wsDep`: `watchableStore.Restore` passes its lock's `wsFields 1`, so no
`syncWatchers` has a reader slot out), the writer's fragment (`writerFrag`: the sole writer's, so no
write transaction is open), the writer's retired backend token (`writerOwn γ`); the store is never
compacted (`crevFrozen`); both backends are the real one's instance (`γ.kb`, `d'`). The sole writer
is at `L`: its certificate and every revision token not spent (`2 ^ 63 - 3 - |L|`: with the
budget's bound `|ilog| + ntok + 3 ≤ 2 ^ 63` of the writer's state this makes the committed log
`ilog` exactly `L`) and, for a watchable store's, the outer quarter of the committed log's
authority (`logQ`, its lock's). The restored log `L' = [[], []] ++ R` extends `L` (`applySnapshot`
panics on a snapshot not newer, and the image is of a longer committed prefix of the same raft
log), each of its revisions has a change, it is well formed and puts no lease (`restoreLogOk`), and
the caller certifies it (`certOk`). The new backend: its contract at every physical names of its
bucket and instance with the witness `True` (`storeBackendT`; `storeBackendT_of_backend`) and its
clean-view `ReadTx` (`keyCleanRead`, `keyCleanRead_of_backend`: the restore plan's R5c), its clean
view (a fresh backend's read buffer is empty: `kbViewC`, R5a)
of the `Key` bucket holding `L'` (all of it), no compaction recorded (`kbNoCmp`), the right to
register a store in it (`kbRegRight`: its batch lock holds `lateW` unregistered) and its readers'
tokens (`nReaders`, `backend.newPost`'s).

**Why it is true of the Go code** (`kvstore.go:292-314` at the etcd pin, `188113160`; the proof's
steps):
* `s.mu.Lock()`: `muInv s γ 1` (from `isStore`'s guard): a half of the fields, all of `s.mu`'s
  deposit ghost (`γ.wr`); the compaction revision is `-1` (`crevFrozen`); with the closer's and the
  caller's quarters the fields are whole (`fieldShare_gather`).
* `close(s.stopc)` with the closer's `stopCloser`; `s.fifoSched.Stop()` with its stop token and
  queue (`Scheduler.Stop`'s spec: it waits for a running job; none runs, `crevFrozen`).
* `s.b = b'`, `s.kvindex = newTreeIndex(s.lg)`: `newTreeIndex` with fresh event-count and
  compactor names, the history, committed-log and compaction names the store's (`idx_renew`).
* `s.revMu.Lock()`; `currentRev = 1`; `compactMainRev = -1`; `s.revMu.Unlock()`: the takeover
  (`restore_takeover`): `s.revMu`'s body (the fields' half of the restoring flag says it is not
  restoring) and the writer's state (its invariant opened: `s.mu`'s whole deposit ghost excludes a
  writer's deposit) out; the committed log is `L` (the revision tokens of `L` the caller holds are
  all the budget leaves), and the committed log, its authority and the index's history move to `L'`
  (`L <+: L'`, `histOf_mono`); the writer's invariant left restoring (the deposit ghost and half the
  history's authority, `writerInvBody`); the lock released in restoring mode (`revMuRest`: its
  halves of the counters), the flag raised; every verified reader of `s.revMu` holds `s.mu` or the
  watchable store's lock (held by the caller), so none sees it.
* `s.fifoSched = schedule.NewFIFOScheduler(s.lg)`, `s.stopc = make(chan struct{})`: a new scheduler
  (its names, stop token and queue) and stop channel; the new backend's names allocated (the batch
  lock's invariant `P'`, key and view log, the compaction's record).
* `s.restore()` over `b'` (`store.restore`'s spec, with data `R`): its `Key` bucket read through a
  `ReadTx` (a new reader token lent), the index rebuilt at `L'`, no compaction (`kbNoCmp`), no lease.
  Its lock of `s.revMu` finds the restoring mode; its unlock is the switch (`restore_switch`): all
  of `cur` (the fields' half, the writer's fragment, `s.revMu`'s and the writer's invariant's eighths
  from the takeover, the readers' pool's) moved to the new objects and `p'`; the readers' pool
  refilled with `k` slots of the new index and backend, the old ones' tokens out (D22 receiver
  epochs, S8d, W7, 2026-10-25: `k = nReaders - 2`, the pool's retired count being the writer's
  `retiredAt γ 2`, and no slot out: none under the watchable store's lock, whose deposit the caller
  holds, none under `s.mu`, whose deposit ghost the writer's invariant holds whole while restoring); the revision budget's tokens of `L'` made; `s.revMu`'s body at
  `γ'` (the restored bucket's view, `certOk γ L'`, the index's count of `L'`, the certificate of
  `L'`: its changes below the receipts' bound, which the rebuild's receipts give, `restore`'s unlock
  argument); the flag down.
* After `restore` (`restore_finish`): the writer's state at `L'` (the rebuild's receipts,
  `currentRev`'s other half) checked in at `γ'`, with the new backend's registration pending
  (`writerReg`: the batch lock's resource at `γ'`) — `Restore` does not lock the new batch
  transaction, so the store is registered at the next writer's lock (`writerInv_checkout`); the
  fields' shares at the new objects with what they are (`physOk` at `γ'`: the contract,
  `hookP γ' P'`, the new index, the new scheduler).
* `defer s.mu.Unlock()` with `muInv s γ 1` at the new objects.

**Postcondition**: `nil`; at some physical names `p'` of the new backend's bucket and instance,
the new right to close (`storeCloser s γ'`), the watchable store's quarter and deposit back, the
writer's fragment at `γ'`, its retired token of the new backend (`writerOwn γ'`), the new batch
lock's invariant recorded (`hookP γ' P'`: the server's hook is installed on the new backend later,
`hookOk_of_init`), the certificate of `L'`, the revision tokens not spent at `L'`, for a watchable
store's the outer quarter at `L'`; the old backend's reader tokens (`nReaders - 1`: the pool's and
the writer's, exactly; with the storage-version monitor's retired one, all of them, for the old
backend's `Close`, which needs every `bOpen` share: D22 receiver epochs, S8d, W7, 2026-10-25, until
then `k + 1` with `k` unknown) and the new backend's one not used (the monitor's). Nothing persistent is
promised: no fact of the old physical names (`physOk`, `hookOk`, `storeRegd`, `isTreeIndex`,
`idxNevLb`, `compactedAt`) claims they are current (that is `cur`'s, which the old parts no longer
hold), and no fact names a field `Restore` writes (`b`, `kvindex`, `fifoSched`, `stopc`,
`currentRev`, `compactMainRev`: their points-to are in the shares and the locks; `↦□` only in a
compacted store's `storeStop`, excluded). -/
abbrev mvcc.store.Restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d⌝ ∗
      mvcc.storeCloser s γ ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗ mvcc.crevFrozen γ ∗
      mvcc.idxCert γ.idx L ∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) ∗
      (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
      mvcc.certOk γ ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendT b' s (γ.withPhys p) P') ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.withPhys p)) (mvcc.storeRT (γ.withPhys p))) ∗
      mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap ([[], []] ++ R)) ∗
      mvcc.kbNoCmp (some d') γb' ∗ mvcc.kbRegRight (some d') ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloser s (γ.withPhys p') ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.storeRT γ) ∗
      mvcc.storeRT (γ.withPhys p') }}

end spec

end EtcdGrove
end Perennial
