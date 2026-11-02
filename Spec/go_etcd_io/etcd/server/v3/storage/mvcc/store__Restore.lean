/-
`store.Restore` (`kvstore.go`): proved (`notes/restore-plan.md`, R5f, 2026-10-24) over `restore`'s
spec and the ghost moves of `RestoreMoves.lean`; in compaction mode (M2's item 15, 2026-11-02) over
the pieces of `RestoreCmp.lean`. Lean-first (no Rocq counterpart); see
`InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab

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
which extends the store's committed log `L`, in either mode** (D22 receiver epochs, S6, 2026-10-22;
proved in the restore plan's R5f, 2026-10-24; in compaction mode, M2's item 15, 2026-11-02),
returning `nil`. The store's logical names `γ` stay (`isStore s γ`, the committed log, the index's
history, the revision budget, the certificates, the readers' tickets, the compaction permit); its
physical ones move to fresh ones `γ' := γ.withPhys p'` (the new backend's bucket and instance `d'`,
a new index's event count and compactor, a new scheduler's, the new batch lock's invariant `P'`,
key and view log, the compaction's meta record and counter). The mode survives the install: the new
backend compacts iff the old one does (`d'.cm = d.cm`); off, every mode-indexed resource below is
the one before compaction mode (`r = CmpRecs.empty`, `c = -1`: `restoreRightM_off`,
`restoreImageM_off`, `storeBackendTR_empty`, `keyCleanReadR_empty`; `specOff_of_spec`).

**Precondition.** The caller holds every part of the store's current objects and names (`γ.cur`)
not in a lock or an invariant `Restore` takes or opens: what `Restore` takes of the store's right
(`restoreRightM s γ c`: off, the right to close, `storeCloser`, an eighth of the fields, the stop
channel's close, the scheduler's stop token, the compaction queue, with the store never compacted,
`crevFrozen`, `c = -1`; on, the compaction right at the store's compaction revision `c`,
`compactRightR`, which holds the same and the jobs' invariant, whose share of the fields comes back
once `Scheduler.Stop` has waited for the jobs), the watchable store's quarter of the fields with its
deposit ghost (`fieldShare … ¼ ∗ wsDep`: `watchableStore.Restore` passes its lock's `wsFields 1`, so
no `syncWatchers` has a reader slot out), the writer's fragment (`writerFrag`: the sole writer's,
so no write transaction is open), the writer's retired backend tokens (`writerOwn γ`: on, with the
compaction job's reader); both backends are the real one's instance (`γ.kb`, `d'`). The sole
writer is at `L`: its certificate and every revision token not spent (`2 ^ 63 - 3 - |L|`: with the
budget's bound `|ilog| + ntok + 3 ≤ 2 ^ 63` of the writer's state this makes the committed log
`ilog` exactly `L`) and, for a watchable store's, the outer quarter of the committed log's
authority (`logQ`, its lock's). The restored log `L' = [[], []] ++ R` extends `L` (`applySnapshot`
panics on a snapshot not newer, and the image is of a longer committed prefix of the same raft
log), each of its revisions has a change, it is well formed and puts no lease (`restoreLogOk`), the
caller certifies it (`certOk`), and, on, its receipt is persistent (`restoreRcptM`: `⧖ (logCh L')`,
some member's sealed log's). The received image is at compaction records `r` (`restoreImageM d' γb'
L' r`): off, a clean view (a fresh backend's read buffer is empty: `kbViewC`, R5a) of the `Key`
bucket holding all of `L'`, no record (`kbNoCmp`); on, a clean view of the entries the cut of `L'`
at `r.crev` keeps (`entsCutAt`), the records with the compaction-key write right (`kbRecs`), the
compaction keys well formed, and no key put at or below `r.crev` deleted by `L'` (`NoDelPutAt`).
The restored compaction revision is what `restore()` computes from the records, `r.crev`, at least
the store's (`c ≤ r.crev`), and the store's compaction permit holds of both records (`crevPermAt γ
r.finRev ∗ crevPermAt γ r.crev`: the restore raises the compaction revision to them, and every
reader of the permit relies on it). The new backend: its contract at every physical names of its
bucket and instance at the records (`storeBackendTR … r`, given its deletable keys fixed,
`restoreFixM`) and its clean-view `ReadTx` at the records (`keyCleanReadR`, lent the reader's token
and, on, the new backend's unfixed registration `restoreRegM`: `dlInit`), off nothing deletable
(`kbNoDelOff`), the right to register a store in it (`kbRegRight`: its batch lock holds `lateW`
unregistered), its readers' tokens (`nReaders`, `backend.newPost`'s), and, on, the new job's
safe-range slot (`kbSRM`), the write-back supply (`kbWTSupplyM`) and, when the records resume a
compaction, the new backend's unset hook (`resumeHookM`, lent and given back).

**Why it is true of the Go code** (`kvstore.go:292-314` at the etcd pin, `188113160`; the proofs'
steps, `store__Restore.lean` off, `RestoreOn.lean` on):
* `s.mu.Lock()`: `muInv s γ 1` (from `isStore`'s guard): a half of the fields, all of `s.mu`'s
  deposit ghost (`γ.wr`), the compaction revision at `c` (off `-1`, `crevFrozen`); with the
  closer's and the caller's quarters the fields are whole (`fieldShare_gather`).
* `close(s.stopc)` with the closer's `stopCloser`; `s.fifoSched.Stop()` with its stop token and
  queue (`Scheduler.Stop`'s spec: it returns once the worker has run every pending job and exited;
  on, its run token gives the jobs' share of the fields back, `storeStopR_reclaim`, and the last
  job's token the old job's budgets, `compactQueue_stopped`).
* `s.b = b'`, `s.kvindex = newTreeIndex(s.lg)`: `newTreeIndex` with fresh event-count and
  compactor names, the history, committed-log and compaction names the store's (`idx_renew`).
* `s.revMu.Lock()`; `currentRev = 1`; `compactMainRev = -1`; `s.revMu.Unlock()`: the takeover
  (`restore_takeover`): `s.revMu`'s body and the writer's state out; the committed log, its
  authority and the index's history move to `L'` (`L <+: L'`, `histOf_mono`); the lock released
  in restoring mode (`revMuRest`), the flag raised; every verified reader of `s.revMu` holds `s.mu`
  or the watchable store's lock (held by the caller), so none sees it.
* `s.fifoSched = schedule.NewFIFOScheduler(s.lg)`, `s.stopc = make(chan struct{})`: a new
  scheduler and stop channel; the new backend's names allocated.
* `s.restore()` over `b'` (`store.restore`'s spec, with data `R` and records `r`; on, the new
  backend's registration lent to its clean read, then fixed, `restoreRegM_fix`): its `Key` bucket
  read through a `ReadTx`, the index rebuilt at `L'` (on, from the cut's entries), the records read;
  its lock of `s.revMu` finds the restoring mode; its unlock is the switch (`restore_switch`), which
  moves all of `cur` to the new objects and `p'`, refills the readers' pool of the new index and
  backend, makes the revision budget's tokens of `L'`, and sets `compactMainRev` to the finished
  record (on, the compaction revision raised to `r.finRev`, permitted, with the lag to `r.crev`
  after it, `muInvLag`); on a resumed compaction (`r.resumes`), its `compactLockfree(r.schedRev)`
  raises it to `r.crev` and schedules the job under the new compaction right.
* After `restore` (`restore_finish`): the writer's state at `L'` (its persistent receipt) checked in
  at `γ'`, with the new backend's registration pending (`writerReg`); the fields' shares at the new
  objects with what they are (`physOk` at `γ'`).
* `defer s.mu.Unlock()` with `muInv s γ' 1` at the new objects, at `r.crev`.

**Postcondition**: `nil`; at some physical names `p'` of the new backend's bucket and instance,
what the caller's right becomes at the restored revision (`storeCloserM s γ' r.crev`: off, the new
right to close; on, the new compaction right), the watchable store's quarter and deposit back, the
writer's fragment at `γ'`, its retired tokens of the new backend (`writerOwn γ'`), its pin at `L'`
(`writerPin γ' L'`, M2's item 37), the new batch lock's invariant recorded (`hookP γ' P'`: the
server's hook is installed on the new backend later, `hookOk_of_init`), the certificate of `L'`, the
revision tokens not spent at `L'`, for a watchable store's the outer quarter at `L'`, the new
backend's unset hook back (`resumeHookM`), the old job's budgets (`compactJobResM γ.kb`: on, a
reader's token and the safe-range slot) and the old pool's readers (`nReaders - 1 - nJobRd γ.kb`:
the pool's and the writer's; with the job's and the storage-version monitor's retired one, all of
them, for the old backend's `Close`, which needs every `bOpen` share), and the new backend's one
not used (the monitor's). Nothing persistent is promised: no fact of the old physical names claims
they are current, and no fact names a field `Restore` writes (`b`, `kvindex`, `fifoSched`, `stopc`,
`currentRev`, `compactMainRev`: their points-to are in the shares and the locks). -/
abbrev mvcc.store.Restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R → c ≤ r.crev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.restoreRcptM d' ([[], []] ++ R) ∗ mvcc.crevPermAt γ r.finRev ∗ mvcc.crevPermAt γ r.crev ∗
      mvcc.isStore s γ ∗ ⌜∃ d, γ.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM s γ c ∗ mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag γ ∗ mvcc.writerOwn γ ∗ mvcc.writerPin γ L ∗
      mvcc.idxCert γ.idx L ∗ ownToks γ.revs (2 ^ 63 - 3 - L.length) ∗
      (if γ.watchQ then mvcc.logQ γ L else iprop(True)) ∗
      mvcc.certOk γ ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.restoreFixM d' (γ.withPhys p) -∗ mvcc.storeBackendTR b' s (γ.withPhys p) P' r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR b' (mvcc.bucketViewC (γ.withPhys p))
          iprop(mvcc.storeRT (γ.withPhys p) ∗ mvcc.restoreRegM d')
          (mvcc.kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbNoDelOff (some d') ∗
      mvcc.kbRegRight (some d') ∗
      mvcc.restoreRegM d' ∗ mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ mvcc.resumeHookM d' r ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloserM s (γ.withPhys p') r.crev ∗
      mvcc.fieldShare s γ (1 : Qp).half.half ∗ mvcc.wsDep γ ∗
      mvcc.writerFrag (γ.withPhys p') ∗ mvcc.writerOwn (γ.withPhys p') ∗
      mvcc.writerPin (γ.withPhys p') ([[], []] ++ R) ∗
      mvcc.hookP (γ.withPhys p') P' ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
      (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
      mvcc.resumeHookM d' r ∗
      mvcc.compactJobResM γ.kb ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.kb) (), mvcc.storeRT γ) ∗
      mvcc.storeRT (γ.withPhys p') }}

end spec

end EtcdGrove
end Perennial
