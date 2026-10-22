/-
`store.Restore` (`kvstore.go`): the trust boundary (translated, its callee `restore` untranslated
and its body's ghost argument not carried out: D22m decided, D22 receiver epochs S6).
Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- **`s.Restore(b')`: the store restored over a new backend `b'` holding the committed log `L'`,
which extends the store's committed log `L`** (D22 receiver epochs, S6, 2026-10-22; D22m decided:
an axiom until S-g2), returning `nil`. The store's logical names `γ` stay (`isStore s γ`, the
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
bucket and instance with the witness `True` (`storeBackendT`; `storeBackendT_of_backend`), its view
of the `Key` bucket holding `L'` (all of it), no compaction recorded (`kbNoCmp`), the right to
register a store in it (`kbRegRight`: its batch lock holds `lateW` unregistered) and its readers'
tokens (`nReaders`, `backend.newPost`'s).

**Why it is true of the Go code** (`kvstore.go:292-314` at the etcd pin, `188113160`):
* `s.mu.Lock()`: `muInv s γ 1` (from `isStore`'s guard): a half of the fields (`cur` ¼), all of
  `s.mu`'s deposit ghost (`γ.wr`), so the writer's state is checked in (`writerInv`, opened: its
  eighth of `cur`) and no reader slot is out under `s.mu` (`readerPool`, opened: its eighth; the
  `tko` count is `0`), and with the caller's `wsDep` none under the watchable store's lock (`tkw`
  `0`): the pool holds `k ≤ nReaders` slots of the old index and backend, with `k + 1 ≤ nReaders`
  (the caller's retired token is a reader slot of the old backend's read lock too, bounded by the
  lock's `nReaders`: `sync.ownRWMutex`'s discarded authority).
* `close(s.stopc)` with the closer's `stopCloser`; `s.fifoSched.Stop()` with its stop token and
  queue (`Scheduler.Stop`'s spec: it waits for a running job; none runs, `crevFrozen`).
* `s.b = b'`, `s.kvindex = newTreeIndex(s.lg)`: the fields' points-to are whole (`muInv`'s half,
  the closer's quarter, the caller's quarter); `newTreeIndex` with fresh event-count and compactor
  names, the history and committed-log names the store's (its reader slots, `nReaders`).
* `s.revMu.Lock()`; `currentRev = 1`; `compactMainRev = -1`; `s.revMu.Unlock()`: `revMuInv s γ 1`
  (its eighth of `cur`, half the restoring flag; the fields' shares hold the other half), the flag
  raised, the lock released in restoring mode (`revMuRest`: its halves of the counters; `currentRev`'s
  other half is the writer's state's, `compactMainRev`'s `muInv`'s); every verified reader of
  `s.revMu` holds `s.mu` or the watchable store's lock (held by the caller), so none sees it.
* `s.fifoSched = schedule.NewFIFOScheduler(s.lg)`, `s.stopc = make(chan struct{})`: a new scheduler
  (its names, stop token and queue) and stop channel.
* `s.restore()` over `b'` (`store.restore`'s axiom with data, `R`): its `Key` bucket read through a
  `ReadTx` (a new reader token lent), the index rebuilt at `L'` (a time receipt per change: D22h, the
  restore's own steps), no compaction (`kbNoCmp`), no lease; `currentRev = |L'| - 1` and the flag
  down under `s.revMu` again. The ghost state then moves: all of `cur` (the seven parts) to the new
  objects and `p'`; the committed log `γ.clog` (both halves: `revMuRest` holds none of it), the
  committed log's authority (the writer's half, `s.revMu`'s and the caller's quarters), the index's
  history (the writer's authority) and the revision budget (`|L'| - |L|` tokens deleted) from `L`
  to `L'` (`L <+: L'`: the history extends, `histOf` prefix-monotone); the readers' pool refilled
  with `k` slots of the new index and backend; `writerInv` holds the writer's state at `L'` with the
  new backend's registration pending (`writerReg`: the batch lock's resource at `γ'`, fresh key and
  view log, the bucket's half view, the certificate, the compaction's fresh record) — `Restore` does
  not lock the new batch transaction, so the store is registered at the next writer's lock
  (`writerInv_checkout`); `s.revMu`'s body at `γ'` (`certOk γ L'`, the index's count of `L'`, the
  other half view); the fields' shares at the new objects with what they are (`physOk` at `γ'`:
  the contract, `hookP γ' P'`, the new index, the new scheduler).
* `defer s.mu.Unlock()` with `muInv s γ 1` at the new objects.

**Postcondition**: `nil`; at some physical names `p'` of the new backend's bucket and instance,
the new right to close (`storeCloser s γ'`), the watchable store's quarter and deposit back, the
writer's fragment at `γ'`, its retired token of the new backend (`writerOwn γ'`), the new batch
lock's invariant recorded (`hookP γ' P'`: the server's hook is installed on the new backend later,
`hookOk_of_init`), the certificate of `L'`, the revision tokens not spent at `L'`, for a watchable
store's the outer quarter at `L'`; the old backend's reader tokens (`k + 1`: the pool's and the
writer's, for the old backend's `Close`, which needs every `bOpen` share) and the new backend's not
used (`nReaders - (k + 1)`, the storage-version monitor's among them). Nothing persistent is
promised: no fact of the old physical names (`physOk`, `hookOk`, `storeRegd`, `isTreeIndex`,
`idxNevLb`, `compactedAt`) claims they are current (that is `cur`'s, which the old parts no longer
hold), and no fact names a field `Restore` writes (`b`, `kvindex`, `fifoSched`, `stopc`,
`currentRev`, `compactMainRev`: their points-to are in the shares and the locks; `↦□` only in a
compacted store's `storeStop`, excluded).

**What would discharge it (S-g2):** a proof over the translated body once `store.restore`'s pieces
are (`restoreIntoIndex`, `restoreChunk`, `keyIndex.restore`; `store.restore`'s own axiom), with a
`newTreeIndex` spec over the store's history and committed-log names (not `idxFresh`'s), and the
ghost moves above as lemmas of `InvStore` (`cur`'s seven parts gathered and updated, the pool
refilled, the writer's state moved to `L'`). -/
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
      mvcc.kbView (some d') γb' 1 (mvcc.bucketMap ([[], []] ++ R)) ∗
      mvcc.kbNoCmp (some d') γb' ∗ mvcc.kbRegRight (some d') ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ (p' : mvcc.PhysNames) (k : Nat),
      ⌜p'.bucket = γb' ∧ p'.kb = some d' ∧ k + 1 ≤ mvcc.nReaders⌝ ∗
      mvcc.storeCloser s (γ.withPhys p') ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      ([∗list] _x ∈ List.replicate (k + 1) (), mvcc.storeRT γ) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - (k + 1)) (), mvcc.storeRT (γ.withPhys p')) }}

end spec

end EtcdGrove
end Perennial
