# Probe: the compaction specs against their real callers (backend-cmp, 2026-10-30)

The spec-first plan's Probe step (`notes/spec-first-plan.md`, "Probe (was phase 3)") for the
`backend-cmp` stage, on commit `f54288b1d4` (branch `backend-cmp`). The compaction bodies were
already proved over the real backend (the core stage), so this Probe proves nothing new: it checks
the specs' callers and package boundaries by reading. It covers the `cm := true` export
(`mvcc_NewStore_backend_cmp`) followed by `store.Compact`, the glue from `storage.OpenBackend`'s post,
the apply thread's `store.Compact` (M2), and the unfolds across a package boundary in this stage's
proofs. Read-only: no Lean statement or proof changed, and nothing was built (a full build of the
commit was running in the worktree). Time: about an hour and a half of reading.

Rubric (the plan's two tiers): **first tier**, the spec is wrong or unusable for a real caller;
**second tier**, cost or clarity.

## Summary

| # | Tier | Finding | Owner |
|---|------|---------|-------|
| P1 | 1 | `store.Compact.spec` (and `updateCompactRev`, `compactLockfree`) consume `hookIs` and never return it: after one compaction the caller has lost the writer's fragment. It cannot write, compact again or restore | mvcc |
| P2 | 1 | `mvcc_NewStore_backend_cmp`'s client has no source for `storeRT γ`: the export drops `retiredAt`, so no reader can be retired | mvcc |
| P3 | 1 | The server never builds this store: `mvcc.New` → `newWatchableStore` freezes the compaction revision unconditionally (`crevFrozen`), yet at `cm = true` still takes the compaction budgets | mvcc / M2 |
| P4 | 1 | **A compacting store can never be restored**, by three independent statements. So compaction on conflicts with the server's snapshot path (D22) | mvcc / D22 / M2 |
| S1 | 2 | `kbWTSupplyM` has no allocation law; a non-server client can meet it only under a receipt bound stronger than the export states | mvcc |
| S2 | 2 | `writerOwn` is fixed at `retiredAt γ 2`; a compacting server would hold `retiredAt γ 3` | mvcc / M2 |
| S3 | 2 | Boot glue drops what compaction needs (`srSlot`, `fkV`); there is no law for `kbSRM (some d)` | etcdserver / mvcc |
| S4 | 2 | `store.Compact.spec`'s `NoDelPutAt` is due to change in M2 (the Go fix, decision (b)), so the spec is "frozen pending" | M2 |
| S5 | 2 | The backend-to-mvcc boot lemmas (`bOpen_halves`, `bkRTx_of_rdToks`) live in etcdserver; a non-server client needs them too | mvcc |
| U | 2 | 22 unfold sites across a package boundary (list below) | backend, mvcc, schema, Perennial |

The review rounds and the glue had not found P1-P4 or S2, because none of them called `store.Compact`
from a real caller's state: the export's glue stops at `NewStore`'s post. P1 dates from D22's S5b
(`81028d9a76`, 2026-10-22, when `hookIs` gained `writerFrag`), not from this stage. No Go bug found
(I checked `applierV3backend.Compaction`'s ignored `Range` error: at revision 0 it cannot fail).

## 1. The `cm := true` export, then `store.Compact`

`mvcc_NewStore_backend_cmp` (`mvcc/Results.lean:319`) gives these of `store.Compact.spec`'s
premises (`Spec/.../mvcc/store__Compact.lean`):
- `storeCmp γ`, `-1 ≤ c` at `c = -1`;
- `isStore`, `storeStop`, `compactRight γ (-1)`;
- `idxCert γ.idx [[], []]`;
- `hookIs γ Pk #f`.

The client brings the rest:
- the trace (`traceutil.ownTrace`, from `traceutil.New`; fine);
- the critical-section contract `csContract P f Pre Q Post`, one per call (fine; Pk and the hook are
  the client's);
- the reader's token `storeRT γ`, which has no source (P2).

Repeated calls: the success branch returns `compactRight γ rev`, `storeRT γ` and the trace, so
`-1 ≤ c` is kept. But `hookIs` is not returned (P1). As stated, **a client can call `store.Compact`
zero times** (P2). Once P2 is fixed it can call it once (P1).

### P1 (first tier): `store.Compact` loses the writer's fragment

- `hookIs γ P f := hookOk γ P f ∗ writerFrag γ` (`InvStore.lean:1001`); `writerFrag` is an owned
  eighth of `curAt`.
- `store.Compact.spec`, `store.compactLockfree.spec` and `store.updateCompactRev.spec` take
  `hookIs γ P f` in the pre. No post branch gives it back.
- The proof drops the fragment: `store__updateCompactRev.lean:67`,
  `icases (mvcc.hookIs_split γ P f).1 $$ HhookC with ⟨#HhookC, -⟩`. Only the persistent `hookOk` is
  used, for `SetScheduledCompact`'s `LockInsideApply`.
- **Consequence:** after one `store.Compact` the caller has no `writerFrag`. It cannot:
  - call `store.Write` (it needs `hookIs` and returns it);
  - call `store.Compact` again;
  - meet `store.Restore` (it needs `writerFrag`).
- **For the server (M2):** the apply thread's `writerFrag` is inside `txn.kvWriter`, inside
  `apply.kvOwn`. The first compaction entry would destroy the apply thread's writer state.
- **The fix:** return `hookIs γ P f` in every post branch of the three specs. The proof change is to
  frame the fragment instead of `-`. An alternative is to take `hookOk` (persistent), but `hookOk`
  is not what clients hold.
- **The same pattern elsewhere:** `writeView.Put.spec` and `writeView.DeleteRange.spec` also take
  `hookIs` and do not return it. That is outside this stage, but the same check applies.

### P2 (first tier): no `storeRT γ` for the export's client

- `storeRT γ = kbRT (some d) = bkRTx d.γB d.P d.be`, a reader slot of the backend's `readTx` lock.
- `newPost`/`newPostK` give exactly `actualMaxReaders` of them, and `NewStore` takes exactly
  `actualMaxReaders`. The creator has none left.
- The only producers of `storeRT` are `readerPool_retire` and `storeReader_retire`
  (`InvStore.lean:5242`, `:5286`). Both need the creator's half `retiredAt γ n` of the pool's retired
  count.
- `NewStore.spec` returns `retiredAt γ (nJobRd kb)`. `mvcc.NewStore_backend` destructures it with `-`
  (`StoreBackend.lean:169`, the last `-`; `wsDep` is dropped too). So neither
  `mvcc_NewStore_backend` nor `mvcc_NewStore_backend_cmp` gives it.
- The cmp export's docstring says "the caller brings ... the reader's token `storeRT γ` (retiring
  one of its readers)". That cannot be done.
- **The fix**, either of:
  - export `retiredAt γ 1` (and `retiredAt γ (nJobRd …)` in `mvcc_NewStore_backend`). The client then
    retires one reader with `storeReader_retire`, which takes £1, `isStore`, the pin
    `curAt γ DFrac.discard o` from `storeStop_open` (a law; no unfold needed), a reader and
    `retiredAt γ 1`.
  - or have the export retire the reader itself and give `storeRT γ ∗ retiredAt γ 2`.

### P3 (first tier): the server never builds this store

- etcd's server calls `mvcc.New` (`server.go:370`), which calls `newWatchableStore`, which calls
  `NewStore`. `mvcc.NewStore` is called directly only by `etcdutl hashkv` and the benchmark tool,
  neither of which compacts.
- `newWatchableStore`'s proof freezes the inner store's compaction revision **unconditionally**:
  `imod mvcc.crevFrozen_alloc γs ⊤ $$ Hright` (`newWatchableStore.lean:58`). `isWatchableStore`
  carries `crevFrozen γ.st` (`InvWatchStore.lean:1543`). So no watchable store, in any mode, has a
  compaction right. `store.Compact` is unreachable on the server's store.
- Yet at `cm = true`, `New.spec` and `newWatchableStore.spec`:
  - take the compaction budgets (`kbSRM`, `kbWTSupplyM`);
  - keep a reader back for the job (`… - nJobRd kb` readers, `retiredAt γ.st (nJobRd kb)`).

  They pay for a compaction that cannot happen.
- `mvcc_NewStore_backend_cmp` is a correct result about a configuration that no Go caller of
  `Compact` builds.
- The compacting configuration needs:
  - `newWatchableStore.spec`/`New.spec` in compaction mode to return `compactRight γ.st (-1) ∗
    storeStop` (through `compactRight_of_closer`) in place of freezing;
  - `isWatchableStore` without `crevFrozen` in that mode;
  - `syncWatchers`/`rangeEvents` over a compacted store. M2's S1 draft 4 plans "no watchers in
    compaction mode" for this, and it is not done.

## 2. The glue: `OpenBackend`'s post to `mvcc_NewStore_backend_cmp`'s pre

A client (the server's boot, or any other creator) does the following.

```
-- before OpenBackend: allocate the late registration gx (dghostVar gx at none, halves:
-- W := lateW gx for the batch lock, lateReg gx kept); choose Pk, the hook f ≠ nil, K := bFresh
b, γ ← storage.OpenBackend cfg h P D (W := fun _ => lateW gx) (Pk := fun _ => Pk) (K := bFresh)
  post: newPostK γ P W Pk bFresh b D
      = isBackend ∗ isStopChans ∗ bFresh γ (ownToks γ.wb wbInit ∗ bOpen γ 1) ∗ bViewC … ∗
        plHook γ nil ∗ rbOwn ∗ actualMaxReaders × rdTok ∗ dlInit γ ∗ fkCl γ P D ∗ srSlot b
let d : KBReal := {γB := γ, be := b, gx, cm := true, …}     -- P = d.P (KBReal.P), hP : bridgeParams d.P
backend.SetTxPostLockInsideApplyHook f; persist  → plHookRO γ f        (as NewServer does)
```

| Pre conjunct | Source | Status |
|---|---|---|
| `isPkgInit` mvcc/backend/schema | the client's | ok |
| `isBackend d.γB d.P (lateW d.gx) Pk d.be` | `newPostK`'s `isBackend` at `W := lateW gx` | ok |
| `plHookRO d.γB f` | the hook setter's post, from `plHook γ nil` | ok |
| `keySized d.γB d.P d.be` | none: a genuine assumption (fewer than `2^62` keys in a read's state; `etcdserver/Results.lean` docstring) | an assumption, as before this stage |
| `dlInit d.γB` | `newPostK` | ok |
| `fkV d.γB true` | `fkCl` via `mvcc.bkNoCmp_fkV_of_fkCl` (needs `noCmpData D`) | ok, but `bootBackend_of_newPost` uses `bkNoCmp_of_fkCl`, which drops `fkV` (S3) |
| `bkView d.γB 1 ∅` | `bViewC` with `D`'s key bucket empty (`hD`) | ok (a new data dir only) |
| `bkNoCmp d.γB` | `fkCl`, with `fkV`, above | ok |
| `lateReg d.gx` | the creator's allocation (the server's: `bootOk`) | ok |
| `wbTok ∗ wbTok` | `bFresh`'s `ownToks γ.wb wbInit`, split | ok |
| `kbSRM (some d)` | `newPostK`'s `srSlot b` | source exists, but `NewServer` drops it (`NewServer.lean:508`, the final `-`); no law gives `kbSRM (some d)` from `srSlot` at `cm = true` without unfolding `kbSRM`/`kbSR`/`kbCmpM` (S3) |
| `kbWTSupplyM (some d)` = `□ (⧗ 1 ={⊤}=∗ wbTok d.γB)` | **none.** The client must build a receipt-backed invariant (as `srvWTPool`) over the remaining `wbInit - 2` tokens, with `receiptBound ≤ n + 1` | **gap** (S1). For the server: R2-7, deferred to M2, which collides with restore (P4) |
| `actualMaxReaders × bkRTx` | `newPostK`'s `rdTok`s and `bOpen γ 1`'s reader shares (`bOpen_one_shares`, `bkRTx_of_rdToks`: in etcdserver's `BootBackend.lean`, S5) | ok |
| `lessorRdOf`, `isLessor`, `rdOwn` | `lease.NewLessor` | ok |
| pure: `hP`, `hcm`, `hcfg`, `hrb` | the client's | `hrb : receiptBound ≤ 2^48` is not enough for `kbWTSupplyM` (S1) |

Then for each `store.Compact`:

| Premise | Source | Status |
|---|---|---|
| `storeRT γ` | none | **gap** (P2) |
| `hookIs` | the export's post | only once (P1) |
| `csContract`, trace, `idxCert … log` with `rev < log.length`, `NoDelPutAt log rev` | the client's own writes (`store.Write` → `End`) | ok (`NoDelPutAt`: S4) |

**The gaps:** `storeRT γ` (P2), `kbWTSupplyM` (S1), a second call's `hookIs` (P1). `keySized` is a
standing assumption. For the server, also the drops in `bootBackend_of_newPost`/`NewServer` (S3) and
the frozen watchable store (P3).

## 3. The apply thread's `store.Compact`: what M2 must do

**The Go path.** `applierV3backend.Compaction` (`apply/backend.go:66`) runs:
1. `traceutil.EnsureTrace(context.TODO(), …)`, which makes a fresh trace;
2. `a.options.KV.Compact(trace, rev)`, the watchable store's embedded `*store`'s `Compact`;
3. `KV.Range(ctx, "compaction", nil, {})` at the latest revision.

`EtcdServer.Compact` (`v3_server.go:382`) proposes `{Compaction: r}`. When `r.Physical`, it also
waits on `result.Physc` and runs `s.be.ForceCommit()` under `s.bemu.RLock()`.

**What exists in this repository:**
- `CompactMode.lean`: the compaction-mode family (`kvInvC`, `reqPropOkC`, `compactClaims`,
  `compactResultIs`).
- `NewServer.specCompact`, a `sorry` (`NewServer.lean:1987`).
- `processInternalRaftRequestOnce.specCompact`, `EtcdServer.Compact` (M2's S3).
- No spec of `applierV3backend.Compaction`. `apply.dispatchOk` still excludes compactions. M2's
  round-1 decision folds the `…C` family back into one, with the Go fix for `NoDelPutAt`.

**To call `store.Compact` with the current specs**, M2 must do the following, in order of dependency:
1. **Fix P1** (`hookIs` returned). Otherwise the apply thread's `kvOwn` cannot survive a compaction.
2. **Give the server's store a compaction right (P3).**
   - `newWatchableStore.spec`/`New.spec` in compaction mode return `compactRight γ.st (-1)` and
     `storeStop` instead of freezing.
   - `isWatchableStore` drops `crevFrozen` in that mode, with `syncWatchers`/`rangeEvents` handling
     a compacted store (S1 draft 4: no watchers).
   - `NewServer`'s proof then calls `compactRight_of_closer`, which gives up `wsCloser`'s
     `storeCloser`. This must come after `NewServer`'s last error return: Go's `defer
     newSrv.kv.Close()` (`server.go:376-381`) closes the store on any later `err != nil`.
   - The apply thread's resources (`kvOwn` or `srvApplyKV`) gain `compactRight γ c` and `storeStop`.
3. **Statement changes, by statement:**
   - **`NewServer.spec`**, merged with `specCompact`: the retention premise (`= 0` or revision mode
     with a positive retention), and the store built at `cm := retention ≠ 0` instead of today's
     `{ d with cm := false }` (`BuildLemmas`, `NewServer`'s proof).
   - **`srvEnvOk`** (`InvApplier.lean:477`): its last conjunct `d.cm = false` must admit `d.cm = true`
     (`d.cm = false ∨ <no snapshot is ever applied>`, or the mode recorded in `E`). Its two
     destructurings in `EtcdServer__apply.lean` follow.
   - **`server_kv_watchable_of`** (`BuildLemmas`): a `cm = true` variant. Its contract comes from
     `storeBackend_of_backendC` with the registration fixed by `storeDlReg` (as `NewStore_backend`
     does internally), not the old bridge's `dlNoDel`.
   - **`bootBackend_of_newPost`/`NewServer`:** keep `srSlot` (S3) and `fkV` (switch to
     `bkNoCmp_fkV_of_fkCl`).
   - **`kbWTSupplyM` (R2-7):** from `srvWTPool` (`srvWTPool ∗ dghostVar E.γbe DFrac.discard d ⊢ □ (⧗ 1
     ={⊤}=∗ wbTok d.γB)`), which discards the server's fraction of `E.γbe`.
   - **`writerOwn`** (`InvStore.lean:3817`, `storeRT γ ∗ retiredAt γ 2`): with `nJobRd = 1` the pool's
     retired count starts at 1, and `NewServer`'s two retirements (`NewServer.lean:616-618`) end at 3.
     It must become `retiredAt γ (2 + nJobRd γ.kb)`, or the job's reader must leave the count (S2).
     `store.Restore` keeps `2` (no restore in compaction mode). The server's reader hand-outs
     (`srvWatchReaders … 64` and the rest) lose one.
   - **The apply's compaction arm:**
     - `apply.dispatchOk` loses its compaction conjunct;
     - a new `applierV3backend.Compaction.spec` over `mvcc_store_Compact`. The apply thread lends
       `storeRT` from `writerOwn` (`writerOwn_rt`), passes `hookIs` (kept by P1's fix) and
       `compactRight`, and gets `rev < log.length` from `compactClaims`;
     - the result's `Physc` (`compactChan`) to the waiter, only if physical compactions are
       admitted. `reqPropOk`'s compaction form excludes them today. A physical compaction's
       `ForceCommit` in `EtcdServer.Compact` needs a reader token and a write-back token of the
       current backend outside the apply thread.
   - **`store.Compact.spec`'s `NoDelPutAt`:** dropped when the fork takes etcd-io/etcd#22377
     (M2's decision (b)). Until then the server needs `irrNoDelPut` on every admitted write (S4).
4. **The restore conflict (P4).** These are D22's statements (the collaborator's track).

### P4 (first tier, the main finding): compaction and snapshot restore exclude each other

A store that compacts can never be restored. This follows from three independent statements, and
weakening any one of them does not remove it:
1. **`store.Restore.spec` takes `storeCloser s γ`.** `compactRight_of_closer` consumes it to make
   the compaction right. A compacting store has given it up for good: `storeStop` says the fields
   are read-only forever.
2. **`store.Restore.spec` takes `crevFrozen γ`**: an invariant holding the compaction right's half
   of the revision's authority at `-1`. That is exactly the half `compactRight` holds. `RestorePre`
   and `SnapApplyDefs` (D22) carry `crevFrozen` too.
   - The root cause is in the ghost design (M2 plan, "Draft, S1 steps 4-5"). `Restore` resets
     `compactMainRev` to `-1`, but the compaction revision's authority is a monotone counter.
     Restoring a compacted store needs that ghost state redesigned.
3. **Q5-3/Q5-4:** `store.Restore.spec` takes `d.cm = false` (old store) and `d'.cm = false` (new
   backend). `applySnapshot.specSnap` and its walk lemmas take `hcm : d.cm = false`.
4. **R2-7, the plan for the server's write-back supply, discards the server's fraction of
   `E.γbe`.** `applySnapshot` must gather all of `E.γbe` to switch backends.

**Today this is not a contradiction for the server.** `applyAll` uses the no-snapshot
`applySnapshot.spec` (`ap.snapshot = nil`, raft's contract). Every server runs under D21 M3's
no-snapshot bound (`receiptBound ≤ SnapshotCatchUpEntries + 1` in `NewServer.spec`): raft's log is
never compacted past index 1, so no snapshot is ever sent. A compacting server under that bound
never restores.

**It becomes one when D22 lifts the bound.** D22 lifts it by wiring `specSnap` into `applyAll`.
From then on, either:
- the compaction mode keeps the no-snapshot bound as a premise (a compacting server is one that
  never installs a snapshot: one member, or the bound). `srvEnvOk`'s `d.cm = false` then becomes
  "`d.cm = false` or no snapshot", and the apply thread needs a fact "no snapshot will arrive" to
  discharge `specSnap`'s `hcm` vacuously; or
- the compaction's ghost state is redesigned so that `Restore` takes `compactRight`. The
  authority's counter must allow a reset at a restore. That is D22's statements (`store.Restore`,
  `watchableStore.Restore`, `RestorePre`, `SnapApplyDefs`, `srvWTPool`) and mvcc's
  (`compactRight`, `crevUB`).

**Production etcd does both:** a lagging follower installs a leader's snapshot (`server.go:1093`,
`s.kv.Restore(newbe)`) while compaction runs (Kubernetes' apiserver compacts every 5 minutes). So
the verified configuration excludes the common multi-member deployment with compaction. That is a
scope decision for the user, not a defect of this stage. But `mvcc_NewStore_backend_cmp`'s "never
closed or restored" (accepted 2026-10-30) commits to the first option until the second is designed.

## 4. Unfolds across a package boundary

These are in the lines this stage added or changed (`git diff 22e0f6d260..f54288b1d4`, first-parent,
`Proof/`). Unfolds of a proof's own package are omitted, as are Perennial's proof-mode patterns.
**22 sites:**
- 15 mvcc → backend/schema;
- 2 etcdserver → backend;
- 4 etcdserver → mvcc;
- 1 mvcc → Perennial.

Each is a missing law of the owning package.

**mvcc proofs unfolding backend's definitions** (`mvcc/Image.lean`, `mvcc/BackendBridge.lean`):

| # | Site | Unfolds | Missing law (owner: backend) |
|---|------|---------|------------------------------|
| 1 | `Image.bkNoCmp_of_fkCl` | `fkCl` | `fkCl`'s parts: `fkCl γ P D ⊣⊢ fkOwn γ (fkInit D) ∗ fkV γ (fkWInit P D)` |
| 2 | `Image.fkV_of_fkCl` | `fkCl`, `fkWInit` | the same, plus `fkWInit_of_abs` (`fkAbsD D → fkWInit P D = true`) |
| 3 | `Image.bkNoCmp_fkV_of_fkCl` | `fkCl`, `fkWInit` | as 1-2 |
| 4 | `Image.fkCl_wf` | `fkCl`, `fkWInit` | `fkWInit_of_wf` |
| 5 | `BB.key_not_fk` | `fkKey`, `schema.keyName` | `fkKey_iff` (which buckets and keys are tracked), stated at schema's names |
| 6 | `BB.fkKey_meta` | `fkKey`, `schema.metaName` | as 5 |
| 7 | `BB.rt_metaNone` | `kvsOutRd` | `UnsafeRange`'s output law (`kvsOutRd_lookup`/`_none`) |
| 8 | `BB.rt_metaWf` | `kvsOutRd`, `rdSlices` | as 7, plus the slices' contents |
| 9 | `BB.bt_metaPut` (changed lines) | `fkPut` | `fkPut_meta : fkKey b k → fkPut … = …` |
| 10 | `BB.sData_delKey_lookup` | `sData` | a lookup law of the model's `sData` |
| 11 | `BB.thinV_delKey` | `thinV` | `thinV`'s deletion law |
| 12 | `BB.bt_rangeC` | `rdB`, `hkPut`, `BParams.hk`, `schema.metaName`, `fkPut` | `rdB`'s open law; `hkPut_of_not_hk`; `fkPut_meta` |
| 13 | `BB.storeDlReg_congr` | `dlIs`, `dlReg` | `dlReg_dlIs : dlReg γ Φ ∗ dlIs γ x ⊢ ▷ Φ x`; `dlIs_of_dlReg : dlReg γ Φ ∗ □ Φ x ⊢ dlIs γ x` |
| 14 | `BB.storeDlReg_persistent` | `dlReg` | a `Persistent (dlReg γ Φ)` instance in backend |
| 15 | `BB.KBReal_P_HK` | `schema.ciKeyBytes`, `schema.termKeyBytes` | schema's Goose constants, evaluated for `decide`: justifiable (constant values), or schema states their values once |

Items 1-4 are the trusted statement's meaning. `storage.OpenBackend`'s docstring explains its
`fkCl` through mvcc's lemmas 1-4, so `fkCl`'s parts should be a backend law: the trusted
statement's reader then needs no mvcc unfold.

**etcdserver proofs unfolding backend's:**

| # | Site | Unfolds | Missing law |
|---|------|---------|-------------|
| 16 | `BootBackend.bootBackend_of_newPost` | `backend.newPost`, positionally (pattern changed for `srSlot`) | a named split of `newPost`/`newPostK` (backend). Every new conjunct (Q5-2's `srSlot`) breaks each positional pattern: the plan had to list "repair the positional `newPost` patterns" as work |
| 17 | `SnapApplyWalk.applySnapshot_walk` (D22's) | `backend.newPostK`, positionally (`7deaf43ae3`) | as 16 |

**etcdserver proofs unfolding mvcc's:**

| # | Site | Unfolds | Missing law (owner: mvcc) |
|---|------|---------|---------------------------|
| 18 | `SnapApplyWalk.applySnapshot_walk` (D22's) | `simp only [mvcc.kbNoCmp]` | `kbNoCmp_some : kbNoCmp (some d) γb = bkNoCmp d.γB` (simp) |
| 19 | `BuildLemmas.server_kv_watchable_of` | `kbView`, `kbNoCmp`, `kbRegRight`, `kbWT`, `kbRT` at `some {d with cm := false}`, by `rfl` | the instance's laws `kb*_some` (simp lemmas). mvcc's own `StoreBackend` uses the same `rfl`s, which is fine inside mvcc |
| 20 | `NewServer.wp_proofM` | `kbWT`, `kbRT` by `rfl` | as 19 |
| 21 | `BuildLemmas.isBackend_cmOff`/`plHookRO_cmOff`/`keySized_cmOff` | `KBReal`'s record update and `KBReal.P`, by `.rfl` | `KBReal.P_withCm` exists; the field projections are structural. Justifiable, or one `KBReal.withCm` simp set |

**mvcc unfolding Perennial's:**

| # | Site | Unfolds | Note |
|---|------|---------|------|
| 22 | `New.lean:70` | `sync.rwmutex.actualMaxReaders_unseal` (to show `3 ≤ actualMaxReaders`) | a Perennial law on the constant's value or bound; 16 uses repo-wide, a pre-existing pattern (`notes/perennial-changes.md` candidate) |

By the plan's rule ("the freeze requires the list empty, or each remaining unfold justified in
`notes/decisions.md`"):
- Items 1-14 and 16-20 need laws: backend 1-14 and 16-17; mvcc 18-20.
- Items 15, 21 and 22 can be justified: constants, record structure, and a Perennial law pending.

## Second-tier findings, in detail

- **S1, `kbWTSupplyM` has no allocation law.**
  - A non-server creator must unfold `kbWTSupplyM`/`kbCmpM`/`kbWTSupply` and build a receipt-backed
    invariant over `ownToks γ.wb n` with `receiptBound ≤ n + 1`. With `n ≤ wbInit - 2 = 2^40 - 3`,
    that is a stronger receipt bound than the export's `hrb : receiptBound ≤ 2^48`.
  - **Proposed:** an mvcc law `kbWTSupply_alloc : ownToks d.γB.wb n -∗ ⌜receiptBound ≤ n + 1⌝ ={⊤}=∗
    kbWTSupplyM (some d)`, and a docstring on the export naming the bound.
  - In the server, the supply must share `srvWTPool`'s tokens (R2-7). Two separate pools would need
    about twice the receipt bound in tokens.
- **S2, `writerOwn`'s fixed `retiredAt γ 2`** (M2's statement change, above).
- **S3, the boot glue drops what compaction needs:**
  - `NewServer.lean:508` drops `srSlot`;
  - `bootBackend_of_newPost` takes `bkNoCmp_of_fkCl`, which discards `fkV`;
  - no law turns `srSlot d.be` into `kbSRM (some d)` at `cm = true` (`kbSRM_of_kbSR` plus `kbSR`'s
    definition: an unfold). Proposed: `kbSRM_on : d.cm = true → srSlot d.be ⊢ kbSRM (some d)`.
- **S4, `NoDelPutAt`:** `store.Compact.spec` will lose it in M2 (decision (b), the Go fix). Under
  the plan's "frozen pending its callers", `store.Compact.spec` is frozen pending M2.
- **S5, misplaced lemmas:** `bOpen_halves`, `bkRTx_of_rdToks` and `bOpen_one_shares`' use
  (`etcdserver/BootBackend.lean`) are facts about backend's and mvcc's resources that any creator of
  a real store needs. They belong in mvcc's `BackendBridge` (or backend).
- Not a finding, recorded for M2: `mvcc_NewStore_backend` (non-cmp) also drops `retiredAt` and
  `wsDep`. A client of the bare store over the real backend can neither retire a reader nor meet
  `store.Restore`'s `writerOwn`/`wsDep`. It has no such client today.

## What this Probe found that the review and the glue had not

P1-P4 and S2. The reviews (rounds 14-17) checked the export's statement and `NewStore`'s glue, not a
`store.Compact` call from the state they produce, nor the server's actual constructor (`New`). As in
M2's `compactableOk` (`notes/spec-first-plan.md`, "The freeze also requires every caller's glue"),
the gap is a caller's glue: here the client of the export, and the apply thread.
