# Scoping the simplest true `Restore` / `applySnapshot`: logical names fixed, physical names existential

Read-only investigation at `lean` = `c7c4b2b441` (worktree `d22`). Go at the etcd pin `2aed163b`
(`etc/goose.py:164`). Note: `.lake/go-src/etcd` is checked out at `107edf7`, not at the pin, so every
Go line below is from `git -C .lake/go-src/etcd show 2aed163b:<file>`. Lean paths are relative to
the repository root; `mvcc/` is `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`, `srv/` is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/`.

## 0. Verdict

The user's direction works for most of the development, with three corrections.

- **No epoch numbers are needed.** The store keeps one `γ : StoreNames`. Its logical names (the
  committed log, the index history, the revision budget, the compaction revision, the certificates,
  the leases) stay fixed: the restored state extends the old one monotonically. The physical names (a
  backend's views and tokens, an index's event count and compactor, a scheduler, a batch lock's
  invariant) become an existential `π` inside the lock invariants. A new ghost variable `γ.cur`
  holds the current `π`. It is not a counter: its only job is to make every share of the lock
  invariants agree on `π`. About **313 of the 457** files that mention the store's or the server's
  names change in no way (§2), because the predicates they use keep their signatures and read only
  logical names.
- **Correction 1: the writer's logical state is stuck in the old backend's batch lock.**
  `writerRes` (`mvcc/InvStore.lean:1394-1408`) holds half the committed log's authority (inside
  `idxWriter`), half of `clog`, half of the revision budget, the history's authority with its
  receipts, and **half of `s.currentRev`'s Go points-to**. It sits in the old backend's batch lock
  (`lateW`, `:1418-1421`). `store.Restore` never takes that lock (`kvstore.go:292-314`), and a Go
  lock invariant cannot be cancelled. So `Restore` cannot write `s.currentRev`
  (`kvstore.go:305`, `:367`), and it cannot extend the log, under any design. **The written D22m
  design has the same gap.** It only says that the new epoch's `writerRes` is "deposited at the
  epoch's first write"; it does not move the old one. The logical half of `writerRes` must therefore
  move out of the batch lock into an invariant gated by `s.mu` (step S2 below).
- **Correction 2: some bounded or exclusive tokens are held outside the lock, so tickets are still
  needed.** This covers the index's `RWMutex` reader slots, the backend's `rdTok`, and the `bOpen`
  shares that `oldbe.Close` needs back in full (`backend__Close.lean`: pre `bOpen γ 1`). Go itself
  holds the lock for the whole use (§3). But a reader *owns* its slot and token between
  transactions (`storeReader`, `InvStore.lean:1928-1935`). Under the user's plan this becomes **one
  pool invariant per store whose contents `Restore` swaps**, not one pool per epoch.
- **Correction 3: the `revMu` window.** `Restore` releases `revMu` with `currentRev = 1`
  (`kvstore.go:302-307`) and sets the real value later (`:365-387`). So `revMuInv` needs a
  "restoring" mode that only `s.mu` or watchable-`mu` holders can rule out. Every verified reader of
  `currentRev` holds one of those two locks (§3). D22m does not mention this either.

With these three corrections, `store.Restore`, `watchableStore.Restore` and `applySnapshot`'s own
stores (`s.be`, `s.uberApply`, `s.alarmStore`) all get specs that are true of the Go code, as axioms
first (§4, S6-S8).

## 1. Logical vs physical names

### 1a. `StoreNames` (`mvcc/InvStore.lean:100-157`) and `IdxNames` (`mvcc/InvIndex.lean:614-622`)

| name | where its authority lives | class | restore as a monotone update of the same name? |
|---|---|---|---|
| `idx.log` (committed log, monotone list) | ½ writer (`idxWriter`, `InvIndex.lean:946-949`, inside `writerRes`), `revQ` in `revMuInv` (`InvStore.lean:1657`), ¼ watchable `s.mu` (`logQ`, `:1588`) | **logical** | yes: the old log is a prefix of the image's log (`kvModel` = `kvRaftOf`, `kvRaftOf_prefix`, `KVModelDefs.lean:369`; `applySnapshot` panics if `snapi ≤ appliedi`, `server.go:1039-1047`). Needs the writer's half, which today sits in the old batch lock (Correction 1). |
| `idx.hist` (index history, monotone list) | authority with the writer (`idxWriter`); lower bounds in `idxLockInv` (`InvIndex.lean:840-848`), `idxCert`, `idxSealed` | **logical** | yes: `histOf` is prefix-monotone (`histOfFrom_append`, `Hist.lean:90`). At `Restore` no write is open, so the writer is `idxWriter γ ilog []` and `histShape ilog [] = histOf ilog`. Same stuck-authority problem as `idx.log`. |
| `idx.crev` (compaction revision) | `crevUB` parts in `muInv`/`revMuInv`/`compactRight`; the server freezes it (`crevFrozen`, `InvStore.lean:1171`) | **logical for a frozen store** | yes at `-1`: `Restore` sets `compactMainRev = -1` (`kvstore.go:306`), so the value does not change. Not monotone for a compacted store, whose spec must exclude it (premise `crevFrozen γ` or `compactRight γ (-1)`). |
| `idx.nev` (event count) | `monoNatAuthOwn` **in the old index's `RWMutex` invariant** (`idxLockInv`, `InvIndex.lean:843`) | **physical** | no. The authority is in the old index's lock, which `Restore` never takes (Go builds a fresh index, `kvstore.go:301`). The lower bound is also inside `idxCert` (`InvIndex.lean:1098-1101`), so `idxCert` must be split: the logical cert (history and log lower bounds plus pure facts) stays, and the count lower bound goes to the readers' `idxKnows .cert` (`InvIndex.lean:1309-1311`) from the current physical names. |
| `idx.cmp` (compactor) | ½ `idxLockInv`, ½ compactor | physical | no; fresh per index |
| `clog` (ghost variable, log) | ½ `revMuInv`, ½ `writerRes` | logical | yes (a ghost variable can be overwritten), once its writer half is out of the batch lock |
| `revs` (revision budget) | ½ `revMuInv`, ½ `writerRes`; the sole writer holds every unspent token (`soleWriter`, `txn/SoleWriter.lean:89-91`) | logical | yes: the caller gives `Restore` `|L'|-|L|` tokens to burn, and `soleWriter γ L` becomes `soleWriter γ L'` (`soleBudget`, `:55`). Needs the writer half. |
| `cok` (certificates) | the caller's map, `kvInv` | logical | yes: the server mints `certOk` of the image's log (S-j2 item 6) |
| `leases` | the lessor (an object that survives restore) | logical | unchanged |
| `watchQ` | flag | logical | unchanged |
| `kb` / `bucket` (backend instance, view) | backend | physical | — |
| `hook`, `hookFn` (batch lock's `P`, the hook) | per batch lock (`hookP`, `:562`; `hookIs`, `:573`) | physical | — |
| `cmeta`, `fin` (`compactRes`, `:1378`) | in the batch lock's `W` | physical | can stay inside the old lock: per backend, never needed again |
| `sch` (scheduler) | scheduler | physical | `storeCloser`'s stop token is spent by `Restore` (`close(s.stopc)`, `fifoSched.Stop()`, `kvstore.go:296-297`) and a new one made (`:310-311`) |

The **index's** lock holds only physical authority (`nev`, `cmp`), so `Restore` never needs to take
it. The **old backend's batch lock** holds logical authority (through `writerRes`) and cannot give it
up: it is a Go `RWMutex`/`Mutex`, so it cannot be cancelled, and `Restore` cannot acquire it.

- **Fix (S2):** the batch lock's `W` keeps only per-backend things: a key `wKey d` (exclusive, per
  backend), `bucketView ½` and `compactRes`. The logical part of `writerRes` (log, `clog`, `revs`,
  history with its receipts, `currentRev ↦ ½`, `lessorRdOf`) moves to a permanent Iris invariant
  `WI s γ := ∃ π, cur γ ½ π ∗ (writerL s γ π ∨ wKey π ∗ wDep γ)`.
- A writer, holding `s.mu` read-locked and the batch lock (and so `wKey π`), checks `writerL` out. It
  leaves the key and `wDep`: a piece of an exclusive ghost variable `γw` taken from its
  `muInv rfrac`, where `muInv q` carries `ghostVar γw q ()`. It checks `writerL` back in before
  `tx.Unlock()` and `s.mu.RUnlock()` (the order of `kvstore_txn.go:209-221`).
- `Restore`, holding `s.mu` exclusively, has `muInv 1`, hence all of `γw`. So no deposit exists, and
  `writerL` is in `WI`. It takes it, extends the log, history and budget, and puts it back at `π'`.
- A cancelable invariant is not needed (Iris has them, `Iris/Instances/Lib/CInvariants.lean`, but
  every opener would then hold a token fraction, which amounts to tickets again).

### 1b. The server's names

| name | class | why |
|---|---|---|
| `ApplyNames.ci`, `.st` (`srv/InvApply.lean:81-93`) | logical | `ciIdx`, apply state; the consistent index object survives (`SetBackend`, `server.go:1073`) |
| `ApplyNames.mt`, `.wr`, `.pend`, `.m0` | **physical** | ½ `mt` and the `pend` token sit in the old batch lock (`batchLockInv`, `InvApply.lean:144-145`); `m0` is "the meta keys the backend was opened with" (the image's `(i, t)` after a restore). `consInv` (`:128-133`) becomes `∃ πA, curA ½ πA ∗ …` with the other half in `applyThread`. Only the apply thread opens it (the hook runs only on `LockInsideApply`). |
| `TM` (`metaTM d.γB d.P`, `CindexBackend.lean:181`), `E.P`, `E.f` (`apply/Chain.lean:278-283`) | physical | the batch lock invariant and hook of one backend |
| `applyBackend γ ci b` (`InvServer.lean:93`) | physical, owned | already the apply thread's (`ciOwner`), moved by `SetBackend` |
| `hookSpec γ ci TM f` (`InvServer.lean:102`) | physical, **stays persistent** | a triple parametric in `γ`: still true after the swap; the apply thread uses it at the new names |
| `srvWTPool γ γp` (`InvApplier.lean:731-733`) | the counter `γp` is logical; the content is physical | a permanent `inv` holding the **old** backend's `wbTok`s for ever. It becomes `∃ π` pinned by the server's current-backend ghost variable, and its stock is refilled from the new backend's `wbInit` (D22h; the closed theorems' `n + 7 ≤ wbInit` holds for every backend). |
| `srvSVRes s γ` (`InvStorageVersion.lean:67-72`) | physical, kept for ever | see §2(c) item 9 |
| `ReqNames ρ`, `ReadNames γr`, `KVNames`, `γw`, `γrev` | logical | the request path, the wait registry, the KV model |

## 2. File classification

Method: a scan of every `.lean` under `Proof/` and `Spec/` (cache/v3, which has its own
`StoreNames`, excluded) that mentions the store's or the server's names. 457 files. Each is
classified by which definitions it mentions or unfolds, then the hard cases were reviewed by hand.
The scripts and full lists are in `/home/ubuntu/.claude-D/jobs/f285f0a4/tmp/` (`classify2.py`,
`count2.py`, `class2.txt`, `listB.txt`, `listC.txt`).

- **(a) unchanged**: the file uses only predicates whose signatures stay and which read only
  logical names: `isStore`, `isWatchableStore`, `txn.isKV`, `storeReader`/`storeReaderC` (as
  tickets), `idxCert` (without the count), `idxSealed`, `certOk`, `soleWriter`, `kvWriter`, `isTxn*`,
  `AEnv` and `E.γ`. The apply proofs that only pass `E.P`/`E.f` generically are in (a), because the
  apply thread moves to `E' = {E with P, f}`. So are the `treeIndex__*` files: the tree's
  `IdxNames` becomes `{γ.idx with nev := π.nev, cmp := π.cmp}` and the readers get the count lower
  bound through `idxKnows`, whose signature stays.
- **(b) small**: the file unfolds a definition whose body changes, and the use happens inside a
  locked operation: Go holds the lock throughout, so the lock invariant's `∃ π` gives the facts for
  the duration.
- **(c) hard**: physical facts are held across an unlock, or a persistent fact goes stale (a Go
  points-to of a written field, a backend-specific contract).

| directory | a | b | c |
|---|---|---|---|
| Proof/…/storage/mvcc | 31 | 23 | 24 |
| Spec/…/storage/mvcc | 35 | 16 | 22 |
| Proof/…/etcdserver (top) | 17 | 18 | 9 |
| Spec/…/etcdserver (top) | 17 | 9 | 6 |
| Proof/…/etcdserver/txn | 16 | 7 (4 of which only unfold the unchanged `soleWriter`/`kvWriter`: likely no edit) | 0 |
| Spec/…/etcdserver/txn | 15 | 3 (`hookIs` framing) | 0 |
| Proof/…/etcdserver/apply | 18 | 0 | 2 (`Contracts`, `Chain`) |
| Spec/…/etcdserver/apply | 67 | 0 | 0 |
| Proof+Spec cindex | 8 | 0 | 0 |
| Proof+Spec v3rpc | 14 | 0 | 1 (InvQuota) |
| lease, auth, v3alarm, backend specs | 0 | 1 (`backend__Snapshot`) | 3 (`NewLessor`, `NewAuthStore`, `NewAlarmStore`) |
| client/v3 (+recipes) | 20 | 0 | 0 |
| examples (Proof+Spec; kv, putget, putget3, watchkv, linkv*, cachekv) | 55 | 0 | 0 |
| **total (457)** | **313** | **77** | **67** |

The (b) files are listed in `listB.txt`. In mvcc these are `InvIndex`, `InvCompact`,
`BackendBridge`, `StoreBackend`, `newTreeIndex`, `newWatchableStore`, `SyncWatchersLemmas`, the four
`storeTxnWrite__{put,delete,deleteRange,Range}` (`storeW`/`bucketView`), the `treeIndex__*` specs
and proofs (no edit needed if the tree's names are the record update above), and the `hookIs`-framing
specs (`writeView__*`, txn `Put`/`DeleteRange`/`Txn`). In the server: `BuildLemmas`, `InvBoot`,
`InvServer`, `CindexBackend`, `EtcdServer__apply*`, `run`, `start`, `InvRun`, `InvApplyAll`, `Results`.

### (c), precisely: what each actually needs

**Store side** (`mvcc/`):

1. **Read transactions.** `store__Read`, `storeTxnRead__End`, `storeTxnCommon__{rangeKeys,Range}`
   and `FrozenSpecs` (Proof and Spec). `storeReader` owns `idxReader ti γ.idx` and `storeRT` across
   transactions, with `s.kvindex ↦□` (`InvStore.lean:1913-1935`).
   *Needs:* `storeReader := s.mu slot ∗ s.revMu slot ∗ ticket ∗ crevFrozen`, and one pool invariant
   `∃ π, cur γ ½ π ∗ (per ticket: idxReader π.ti ∗ kbRT π.kb) ∗ (checked-out deposits)`. A ticket is
   checked out at `Read` (under `s.mu` read-locked, agreeing on `π` via `muInv`) and checked in at
   `End`.
2. **Write transactions.** `store__Write`, `storeTxnWrite__End`, `watchableStore__Write`,
   `watchableStoreTxnWrite__End` (Proof and Spec). *Needs:* the `WI` checkout of §1a, and
   `storeWT`/`hookIs` as the writer's "current" facts (below).
3. **The watch side.** `watchableStore__{syncWatchers,moveVictims,watch}`, `rangeEvents`. These read
   `s.store.b` and `currentRev` under the watchable `s.mu` and `revMu`, not `store.s.mu`
   (`watchable_store.go:358-375`, `:321-323`, `:141-143`). *Needs:* a share of `cur` and of the `b`
   field points-to in `watchStoreInv`, and a second kind of pool checkout and deposit under the
   watchable lock. `watchReader` (`InvWatchStore.lean:1486`) keeps its signature. D22m's
   `WsOk.st_flags` relaxation is still needed: `watchableStore.Restore` sets `restore = true`
   (`watchable_store.go:215-219`).
4. **Compaction.** `store__{compact,scheduleCompaction,compactBarrier,compactLockfree,updateCompactRev,Compact,checkPrevCompactionCompleted}`,
   `store__Close`, `watchableStore__Close`. The job runs on the scheduler goroutine **without
   `s.mu`** and reads `s.b` and `s.kvindex` (`kvstore.go:234-260`, `kvstore_compaction.go:28-…`).
   *Needs:* the physical facts and a share of the fields' points-to inside `compactRight` and
   `storeCloser` (exclusive, held by the compactor or closer). No ticket is needed. `Restore`'s spec
   requires a frozen store, which the server is; the frozen state is reached by giving up the
   compaction right (`InvStore.lean:1164`), so no job ever exists.
5. **Allocation and definitions.** `InvStore`, `InvWatchStore`, `NewStore` (Proof and Spec). These
   allocate `cur`, `WI` and the pool, and redefine `isStore` without `↦□` of `b`, `kvindex`,
   `fifoSched` and `stopc` (`:1859-1885`).

**Server side** (`srv/`, Spec `etcdserver/`):

6. **`Backend()` callers.** `EtcdServer__Backend`, `v3rpc/InvQuota`. Go uses the returned backend
   after `RUnlock` (`server.go:2401-2405`): the quota's `Size()` may run on a closed backend. *Needs:*
   only the persistent `isBackend`, which `backend__Size`'s spec requires. No tokens.
7. **`s.be`.** `NewServer` (`NewServer.lean:860-866` persists half of it), `SnapSendBranch:66` and
   `EtcdServer__createMergedSnapshotMessage` (`s.be ↦□`), `InvApplyAll` (`bemuP`, `:61-62`).
   *Needs:* the apply thread's own half, not persistent. Go's apply thread is `s.be`'s only writer
   (`server.go:1096`) and reads it without `bemu`. `bemuP q := ∃ c, s.be ↦{q/2} ∗ curBe frag`.
8. **The apply thread's field facts.** `InvApplier` (`srvFieldsAt`, `:471-490`: `↦□` of
   `uberApply` and `alarmStore`, `⌜E.P = batchLockInv γ TM⌝`), `InvBuild:232,325`, `InvStart:73-77`,
   `InvApply` (`consInv`), `EtcdServer__restoreAlarms` and `EtcdServer__NewUberApplier` specs.
   *Needs:* these become the apply thread's (non-persistent) record, threaded through `run`'s loop
   invariant (`∃` record). This is S-j2 item 2's `SrvEpoch` without the epoch: only `bemu` and
   `consInv` need a ghost variable.
9. **The storage-version monitor.** `InvStorageVersion`, `EtcdServer__monitorStorageVersion`.
   `srvSVRes` keeps `bkRTx` and `wbTok` of one backend for ever. *Needs:* a one-ticket pool under
   `bemu`. Go holds `bemu.RLock` for each use (`adapters.go:76-81`, `server.go:2207-2217`).
10. **Persistent backend-specific contracts.** `apply/Contracts` (`isApplyLessor`, `isAuthStore`,
    `isAlarmStore`, `isCluster`, `:174/268/334/410`), `apply/Chain` (`:763-812`), `InvRead:127-128`
    (the request path keeps them at `E.P`/`E.f`), and the `NewLessor`/`NewAuthStore`/`NewAlarmStore`
    specs (e.g. `NewAlarmStore`'s post `⌜γ.kb = some d⌝ -∗ apply.isAlarmStore a γ Pk f`). After
    `Recover`/`SetBackend` these objects write through the **new** batch lock, so a persistent triple
    over the old `P` would be false.
    *Needs:* each object's write triples take an exclusive "on backend `d`" fragment (authority in
    the object's lock invariant; fragment bundled into a resource the apply thread already passes,
    e.g. `leaseOwn`). `Recover`'s axiom swaps it, and the old contracts become vacuously true.
    This is not in the S-j2 design.

**Not verified, recorded for completeness:**
- `hashByRev` uses a backend `ReadTx` after `s.mu.RUnlock()` (`kvstore.go:186-191`).
- `setupMetricsReporter`'s closures capture the old `b` for good, and `reportCurrentRev` reads
  `currentRev` under `revMu` alone, so it can show the window's `1` (`kvstore.go:521-…`; the Go
  comment at `:303` says so).
- `Alarms()`' racy read of `s.alarmStore` (already `issues/etcd-alarm-store-snapshot-race.md`).

## 3. Does Go hold the lock while the physical object is used?

| reader | lock held | evidence | consequence |
|---|---|---|---|
| read transaction, `Read`…`End` | `s.mu.RLock` throughout | `kvstore_txn.go:46-47`, `161-164` | facts while locked suffice; the ticket exists only because slots and tokens are exclusive and bounded and `Close` needs `bOpen 1` back |
| write transaction, `Write`…`End` | `s.mu.RLock` throughout, plus the batch lock | `:174-176`, `209-221` | `WI` checkout |
| `store.Rev()` | through `ReadView` → `Read` (`s.mu.RLock`) | `store__Rev.lean` docstring | ✓ |
| `syncWatchers`, `moveVictims`, `watch` | watchable `s.mu`, plus `store.revMu.RLock`; **not** `store.s.mu` | `watchable_store.go:358-375`, `321-323`, `141` | `watchableStore.Restore` holds the watchable `s.mu` around `store.Restore` (`:207-210`): a share in `watchStoreInv` suffices |
| compaction job | **none** (scheduler goroutine) | `kvstore.go:234-260`, `kvstore_compaction.go:28-` | `Restore`'s `fifoSched.Stop()` (`:297`) waits for the running job and drops queued ones, and the fields are written after it (`:299-311`). The server never compacts, so: facts in `compactRight`, `Restore` on frozen stores |
| `currentRev` readers in the `Restore` window | all verified readers hold `s.mu` (`Read`, `Compact`, `hashByRev`) or the watchable `mu` | as above | `revMuInv`'s restoring mode is never seen by a verified reader |
| storage-version monitor | `bemu.RLock` per use | `adapters.go:76-81`, `server.go:2207-2217` | facts while locked plus one ticket |
| quota / `Backend()` | released before use | `server.go:2401-2405` | needs nothing but persistent `isBackend` |
| apply thread (`s.be`, `uberApply`, `alarmStore`) | none, as the only writer | `server.go:1096`, `1163`, `2414` | owned points-to |

So every class (c) reader except the compaction job and `Backend()` holds the lock for the whole
use, and those two need nothing from a pool. **No per-epoch anything is needed.** The single pool
exists only because a reader's slot and token are exclusive, bounded, and must all return for
`oldbe.Close`.

## 4. The simplest plan, step by step (each step builds; no behavior change until S6)

- **S1. Split the index names and `idxCert`.**
  - `idxCert` drops the `nev` lower bound and `idxKnows .cert` adds it. The tree's `IdxNames` is
    `{γ.idx with nev, cmp := π's}`.
  - `revMuInv` and `muHeld` carry the current count lower bound for the reader.
  - Files: `InvIndex`, `InvStore`, `NewStore`/`newTreeIndex` (allocation), `rangeKeys`/`Range`, the
    15 `idxKnows` users. About 20 files.
- **S2. Move the writer's logical state out of the batch lock.**
  - `W` becomes key, `bucketView ½`, `compactRes`.
  - `WI` holds the logical writer state with the `γw` deposit (§1a).
  - Files: `InvStore`, `BackendBridge`, `StoreBackend`, `NewStore`, `store__Write`,
    `storeTxnWrite__{End,put,delete,deleteRange,Range}`, the watchable `Write`/`End`,
    `scheduleCompaction`/`updateCompactRev` (they keep `compactRes` from `W`), `backend__Snapshot`
    spec. About 15 files.
- **S3. Make the fields and physical facts lock-protected.**
  - `γ.cur` (ghost variable of `π`, the new `StoreNames` field) is shared by `muInv`,
    `watchStoreInv`, `WI`, the pool, `compactRight`/`storeCloser`, and the writer's current
    fragment.
  - The fields' points-to are split among `muInv`, `watchStoreInv`, `compactRight` and
    `storeCloser`; `isStore` becomes guards plus logical facts.
  - `revMuInv` gets the restoring mode (a ghost flag, ½ `revMuInv`, rest in `muInv` and
    `watchStoreInv`).
  - Files: the mvcc (c) items 1-5 that unfold `isStore`. About 25 files.
- **S4. Reader tickets** (one pool per store).
  - `storeReader` keeps its signature as the shared reader.
  - The apply thread keeps its own `storeRT` of the current backend (re-made by `Restore`), so
    `storeReader_rt`'s 22 apply users are unchanged if `kvOwn` (`Chain.lean:306-308`) bundles it.
  - Files: `InvStore`, `store__Read`, `storeTxnRead__End`, `FrozenSpecs`, `syncWatchers`,
    `NewWatchableLemmas`, `Chain`. About 10 files.
- **S5. The writer's current facts.** `hookIs γ P f` (`InvStore.lean:573`) becomes a non-persistent
  fragment of `cur` (the writer is the apply thread, which also restores), and is returned by
  `Write`/`End`. `storeWT γ` stays: the apply thread's `γ` and `E` are updated by record update at the
  swap, and only it holds `storeWT`. About 25 files, mostly framing.
- **S6. Axioms of `store.Restore` and `watchableStore.Restore`**, true of the Go code. About 4 files
  (Spec, Link, `etc/tcb-baseline.txt`).
  *Done 2026-10-22* (`notes/decisions.md`, "D22 receiver epochs, S6 carried out"): `store.Restore`
  an axiom, `watchableStore.Restore` proved over it; it took more than the estimate: the restored
  backend's pending registration (`writerReg`) and the watch side (item 3 there).
  - *Pre:* `isStore s γ`; the watchable `s.mu` share; `storeCloser`; `crevFrozen γ`; the writer's
    `cur` fragment; `ownToks γ.revs (|L'|-|L|)`; `⌜L <+: L'⌝`; `restoreLogOk`; the new backend's key
    contract over `keyImage L'` with `bkNoCmp`; its token stock (`bkRTx`×N, `wbTok`s) and `lateReg`;
    `certOk γ L'`.
  - *Post:* the old backend's tokens (all `bOpen` shares in, by the deposit argument); the new
    `storeCloser`; the writer's fragment at `π'`; `idxCert γ.idx L'`; the time receipts of the
    restore's steps (S-g item 4); for the watchable store, the moved watchers.
- **S7. The server.**
  - The physical half of `ApplyNames` becomes existential in `consInv`, pinned via `applyThread`.
  - `srvFieldsAt`'s `↦□` of the written fields become the apply thread's record.
  - `NewServer` stops persisting `s.be`; `bemuP` gets the backend ghost variable; the monitor gets
    its one-ticket pool; `srvWTPool` becomes `∃` current backend.
  - The contracts get their current-backend fragment, with the `Recover`/`SetBackend` axioms (S-j2
    item 5).
  - Files: `InvApply`, `InvServer`, `InvApplier`, `InvApplyAll`, `InvBuild`, `InvStart`, `InvBoot`,
    `BuildLemmas`, `NewServer` (+spec), `InvStorageVersion` (+monitor), `EtcdServer__Backend`,
    `InvRead`, `Contracts`, `Chain`, `AuthDerive`, the three constructor specs,
    `EtcdServer__{apply,applyEntryNormal,applyAll,run,start}`, `Results`. About 35 files.
  *Done 2026-10-23 but the first bullet* (`notes/decisions.md`, "D22 receiver epochs, S7 carried
  out"): the fields, `bemu`'s ghost variable, the monitor's token in the write budget, and the
  objects' backend fields as their "on backend `d`" fragments (half the lock's, half the user's,
  lent by the write right) instead of ghost variables; `AlarmStore.Recover` proved (+1 axiom,
  `restore`). The apply protocol's physical names (the first bullet) designed there, not done: the
  old backend's `Close` commits through the shared hooks, which a retired set must allow.
- **S8. `applySnapshot`'s spec and proof** (S-j2 item 6, unchanged in substance).
  - `s.be` is written under `bemu.Lock`, with the apply thread's half plus `bemuP 1`.
  - `s.uberApply` and `s.alarmStore` are owned points-to.
  - `go oldbe.Close()` gets `bOpen 1` from S6's post, the monitor pool's swap, and the
    `Recover`/`NewAlarmStore` returns.
  - About 10 files.

**Size:** about 140 files touched, of which about 60 are mechanical (framing, a parameter). **About
313 files are not touched**: txn's 31, apply's 85, the request path, client/v3, every example's
Proof and Spec, and `treeIndex__*`.

### Compared with D22m (A) and S-j2's design

| | D22m / S-j2 | simple plan |
|---|---|---|
| names | `StoreNames` split into object `σ` and epoch `γ`; **every predicate over `γ` restated over `(σ, γ)`** (about 90 files by the notes' count; every holder of `idxCert`/`certOk`/`soleWriter` is affected) | one `StoreNames`, logical names fixed; `π` existential, pinned by `γ.cur` |
| epoch number / `ep` variable | yes (`ep` ghost variable naming the epoch) | no; `cur` holds the physical record itself |
| reader tickets | yes, a per-epoch pool swapped by `Restore` | yes, **one** pool invariant, contents swapped (unavoidable: bounded slots, `bOpen 1` for `Close`) |
| writer's logical state | new per epoch; the old one left in the old lock (**gap**: `currentRev ↦ ½`) | moved out of the batch lock once (S2); extended monotonically |
| `revMu` window | not addressed | restoring mode (S3) |
| logical predicates (KV model, certificates, `kvInv`, clients) | restated per epoch | unchanged |
| `SrvEpoch` with `γep` | yes | the apply thread's existential record; a ghost variable only for `bemu` readers and `consInv` (essentially S-j2 item 2 without restating `isServer`'s users) |
| `srvWTPool` | re-allocated per backend | one invariant, `∃` current backend, stock refilled |
| still needed in both | the old backend's tokens for `oldbe.Close`; the watch flag `restore = true` (`WsOk.st_flags`); closers re-made; the `Recover`/`SetBackend`/`RemoveAllPeers` axioms; `dbOpensOk` and the determinism axiom | same |

**True specs.** Yes, once S1-S5 and S7 are done. No persistent fact names a written field any more,
so `store.Restore`/`watchableStore.Restore` can be stated as true axioms (S6), and `applySnapshot`'s
own stores become provable (S8). `s.alarmStore` is the exception: a *verified* concurrent `Alarms()`
would still need the fork fix of the filed issue, though no verified reader exists today.

## 5. Risks: what could force per-epoch names after all

1. **Persistent backend-specific facts kept for ever.**
   - The apply contracts (§2 c10), `NewAlarmStore`'s `⌜γ.kb = some d⌝` post, `hookIs`, and
     `srvWTPool`'s permanent `inv` holding the old `wbTok`s.
   - If any of these stays persistent and names one backend, it becomes false after a `Recover`
     (an axiom that is false is unsound) or blocks the proof.
   - Each must become an exclusive "current" fragment, or a triple whose precondition requires one.
     This is a mechanical restatement but touches the trust base (the constructor axioms).
2. **`idxCert`'s count part.** Clients keep certificates for ever (`appliedOk`, `InvProposer.lean`
   ~455; client/v3; watch registrations `InvWatchStore.lean:1514-1517`). The scan found the count
   (`.nev`) used only inside mvcc (`InvIndex`, `InvStore`, `treeIndex__{Put,Insert,Tombstone}`), so
   moving it out of the persistent cert is safe. If any kept cert's count part were needed later,
   per-index names would follow it.
3. **`compactedAt` (`γ.fin`, persistent lower bound, physical).** Held only by compacting clients
   in mvcc. `Restore` must exclude compacted stores, or `fin` becomes per backend for them.
4. **`bOpen 1` for `oldbe.Close`.** Every holder of an old share must return it at the swap: the
   store pool, the monitor, and the lessor/auth/alarm/cluster/cindex `Recover` axioms. A share
   lost in a permanent invariant would make `Close`'s goroutine unprovable. A merged snapshot in
   flight holds its own share (bbolt's `Close` waits; liveness only).
5. **Order inside `applySnapshot`.** `lessor.Recover(newbe)` (`server.go:1080`) runs **before**
   `kv.Restore` (`:1087`), and `consistIndex.SetBackend` (`:1073`) before both. So "the current
   backend" is per object, not global: each object needs its own fragment. One server-wide ghost
   variable for the backend is wrong in that window.
6. **Two gaps in the written design (record in `notes/`, not `issues/`).** D22m misses the writer's
   `currentRev ↦ ½` and logical authority stuck in the old batch lock, and it misses the `revMu`
   window. Both are needed by any design.

No Go bug found (no `issues/` entry). The only Go-visible oddity, `currentRev = 1` during `Restore`,
is seen only by the unverified metrics closure and is documented in the Go comment.
