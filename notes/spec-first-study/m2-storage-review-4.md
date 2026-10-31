# M2, the storage side: review round 4 (2026-10-30)

Reviewed: branch `m2-storage`, commit `f3282099c3`. This is round 2 for step 2 (restore in
compaction mode) and the first round for the scheduler Draft (`pkg/v3/schedule/M2StorageDraft.lean`).
Step 1's statements, which converged last round, were checked only for churn.

**Targets**
- Every Draft module (`git ls-files | grep M2StorageDraft`, 12 modules).
- The switched internals: `git diff lean...HEAD -- Proof Spec`, the Drafts excluded. These are
  `writerOwn`/`writerOwn_off`, `bootBackend_of_newPost`'s `fkV`, `InstanceLaws`, and `store__Restore`
  and `NewServer` moved to `writerOwn_off`.
- `notes/m2-storage-plan.md`'s approval list ("After review round 3", items 1-26), compared with
  `lean`.

**Method.** I formed my view from the Drafts, the Go code at the pin (`.lake/go-src/etcd`,
`249d76bea7`) and the callers' proofs. Only then did I read rounds 1-3. I built nothing and ran
nothing. Nothing in the repository changed except this file.

**Go.** I found no new Go bug. Both known bugs are recorded:
- `issues/etcd-restore-pending-compaction-unclosed.md`;
- `issues/etcd-restore-scheduled-compact-zero.md`.

One Go fact matters below (A2): during `kv.Restore` the new backend has no post-lock hook. The hook
is set only after `Restore` returns:
- Go: `server.go:1089-1093`, and `LockInsideApply` skips a nil hook (`batch_tx.go:111-122`);
- the walk follows the same order: `hRst` at `SnapApplyWalk.lean:400`, `hSTP` at `:428`.

**Abbreviations.**
- `mvcc/` = `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`
- `etcdserver/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`
- `schedule/` = `Proof/go_etcd_io/etcd/pkg/v3/schedule/`
- "mvcc R" = `mvcc/M2StorageDraftRestore.lean`

## Summary

**Two first-tier findings, both in step 2's restore chain.**

- **A1.** The generalized inner `store.restore.specR` still takes today's full-bucket
  `restoreView`, whose clean read is at `kbNoCmp`. So:
  - it cannot read an image's records;
  - it cannot take the thinned bucket that `restoreImageM` gives;
  - its post still claims the index of the whole log.

  The same `kbNoCmp`-versus-records mismatch reaches `Restore.specM`'s own `storeBackendT` and
  `keyCleanRead` premises. So `Restore.specM` in compaction mode, for an image with records, can
  neither be met by D22's walk nor proved from `specR`.

  Step 2's own "largest piece" (the index over a thinned bucket) was dropped from the plan in
  round 3's repair, not resolved.
- **A2.** `resumeCsM` asks for `kbHookIs (some d') γb' f`, the new backend's non-nil hook,
  read-only. Before `Restore` returns, no caller can have it, and Go runs no hook in the resumed
  `SetScheduledCompact`.

**Round 3:**
- F1 is half resolved: the records, `CmpRecs.crev` and the write right are right. The inner chain
  is not done (A1).
- F2 is resolved. The scheduler payload is sound and minimal; two switch-time conditions are in S2.

**Churn: none in step 1.** Since round 3 its statements changed only in docstrings, the removal of
`compactRight_of_wsCloser` (asked for) and the new law `isWatchableStore_frozen`. Step 2's changes
are repairs, not reversals.

**The approval list is not complete** (S6).

## The brief's decisions: realized soundly?

- **Restore works in compaction mode; watchers excluded.** The design is sound against Go's order:
  `compactRightR`, `storeStopR` at fixed objects, `storeStopR_reclaim`, `fieldShare_reclaim`, and
  `Stop` returning the run token. The statement chain is not yet usable (A1, A2).
- **The write-back supply, one stock per backend sharing the receipt counter.** Sound. I checked
  the arithmetic of `srvWTStock_take` (`etcdserver/M2StorageDraftRestore.lean:92-116`):
  - `receipt_add_one_lt` gives `a + 1 < receiptBound`;
  - the stock's lower bound gives `m ≤ a`;
  - with `receiptBound ≤ m + n + 1`, that forces `n ≥ 1`;
  - after the take, `m := a + 1` and `n - 1` re-establish the bound.

  Old stocks stay valid, since their lower bounds only become staler. `kbWTSupplyM_of_poolR` is the
  compaction arm's source (round 3's S5, done). The one deviation from "off reads as today" is the
  `£ 1` in the take laws, and the plan now says so (item 21).
- **Compaction revision logical, with `c ≤ c'`.** Sound as a premise: the authority `crevUB γ.idx`
  is monotone and `Restore.specM`'s post raises it to `r.crev`.
  - `CmpRecs.crev` matches Go exactly (`kvstore.go:330-342`, `:383-391`, `:411`, and
    `updateCompactRev :197-222`, which succeeds because `currentRev` was raised to the scheduled
    record).
  - **Where the scope limit "no compaction at revision 0" should sit** (not drafted):
    - **Not** in `store.Compact.spec`. mvcc handles `Compact(0)` correctly, so a premise there is
      an unneeded premise on a library spec ("No unneeded premise").
    - **Not** in `Restore.specM`. `c ≤ r.crev` stays its only premise.
    - It belongs **where a compaction enters the log**: the compactor's request contract
      (`compactableOk` / `EtcdServer.Compact.spec`'s pre: `1 ≤ rev`, marked as M2's scope
      restriction with a pointer to the issue file). M2's `v3compactor` discharges it
      (`revision.go:82` skips `rev <= 0`; the periodic one takes `≥ 1`).
    - The apply side then carries it as an invariant of the committed log. Every committed
      `Compaction` has `rev ≥ 1`, so the KV model's `crevOf A` is `-1` or `≥ 1`.
    - On the storage side, reflect it in `keyImageM`'s on branch (records `≥ 1` in `recsOk`, or
      `r.sched ≠ some 0`). Then `r.crev = crevOf A'` (S-j1's) holds without the corner, and #8's
      `hcc` is `crevOf_mono`. `CmpRecs.resumes` keeps its `≠ 0` test, which is faithful to Go.
    - Uncertain: I did not check how `kvRaftOf` models proposals, so the log invariant's exact
      vehicle is open.
- **Scheduler: `Stop` returns the run token, the barrier a tracked job.** Sound.
  - `updateCompactRev`'s barrier is scheduled inside `Compact`, which holds the right and so the
    queue.
  - The cancelled re-schedule branch is dead once the job learns the payload (`stopc` `Done`).
  - Two conditions at the switch are in S2.
- **Compaction-off statements read as today.**
  - Exact for: `store.Restore.spec_of_specM`, `watchableStore.Restore.spec_of_specM` (at `c = -1`,
    `r = empty`, `Pre = True`), `Close.spec_of_specM`, `srvEnvOkD_off`, and `srvKVCloserM_off` (up
    to `⌜c = -1⌝`).
  - Not as today: `srvWTPoolR` (`£ 1`), which is stated.

## First tier

### A1. `store.restore.specR` and `Restore.specM`'s backend premises still assume no records and a full bucket. Compaction mode with records is neither provable nor usable.

**Principles:** Complete; Sound (the callee spec must be provable); "Every premise has a source the
client sees".

**Evidence.**

1. **`specR` cannot read the records it is generalized for.**
   - `restore()` reads both compaction keys through the `ReadTx` of its clean read (`kvstore.go:327-342`).
   - Today's proof does it with `hFin rt true` / `hSch rt true` (`mvcc/store__restore.lean:93`, `:101`, `:606`, `:614`).
   - The `metaReadSpec rt true` it needs comes from `keyReadLocked`'s clause
     `□ (NC -∗ NC ∗ □ metaReadSpec rt true …)` (`InvStore.lean:734-741`).
   - Here `NC` is `restoreView`'s clean read at `kbNoCmp γ.kb γ.bucket` (`InvStore.lean:4836-4838`).
   - `specR` (mvcc R:741-773) keeps `mvcc.restoreView b γ RT q R` unchanged, while the resource it
     gives is `kbRecs γ.kb γ.bucket r`. For `r ≠ empty`, `kbRecs` is not `kbNoCmp` (it is
     `fkOwn d.γB n` with `n ≥ 1`), so the clause can never be used.
   - Even with `NC := kbRecs r`, today's clause says the read returns *nothing* (`nc = true`),
     which is false of a backend with records.
   - The plan's switch note ("`keyReadLocked`'s meta clause reads `metaReadSpecR rt r` for a new
     parameter `r`") is not reflected in any drafted text. `specR`, `Restore.specM` and the walk
     all pass no `r`.
2. **`specR` takes the full bucket and promises the full log's index.**
   - `restoreView … R` is `bucketViewC γ q (bucketMap ([[], []] ++ R))`.
   - The post, through `revUnlockW`'s `restoreViewOut γ q R ∗ isTreeIndex ti γ.idx`, and the
     `idxLockG`/`idxWriterLb` at the whole log, describes the index of the whole log.
   - `restoreImageM`'s on branch gives a view of a **thinned** `m` (`bucketThinnedAt`), not
     `bucketMap L'`. So `Restore.specM`'s proof cannot instantiate `specR` with what its pre holds.
   - If `specR` were instantiated at a thinned bucket, its post would be false. `restoreIntoIndex`
     (`kvstore.go:430-480`) builds key indexes from the surviving revisions only:
     - a key whose old puts were deleted is rebuilt by `ki.restore` from a later revision;
     - a key with only a tombstone left is rebuilt by `restoreTombstone`.
   - Step 2 called this "the first thing to design … the largest piece" (plan, "Not drafted in Lean:
     `store.restore.spec`", the **gap**: the index over a thinned bucket). Round 3's repair section
     no longer mentions it, and `specR` is described as "today's text with `kbRecs` in place of
     `kbNoCmp`".
   - The resumed job's `treeIndex.Compact` runs asynchronously, *after* `Restore` returns. So the
     store's invariant must also accept an index rebuilt from a thinned bucket while the compaction
     is pending, not only "the log's index, compaction pending".
3. **The same mismatch in `Restore.specM`'s pre** (items 15, 16).
   - `∀ p, storeBackendT b' s (γ.withPhys p) P'` is at `NC = kbNoCmp` (`InvStore.lean:3727-3731`).
   - `specR` wants `isKeyBackendG … (kbRecs γ.kb γ.bucket r)`.
   - `∀ p, keyCleanRead … (kbRecs … r)` (mvcc R:458-460, :554-556) asks the caller for "holding
     `kbRecs r`, meta reads are empty". D22's walk cannot build that over an image with records:
     - its only source, `keyCleanRead_of_backend` (`BackendBridge.lean:3503-3520`), gives `kbNoCmp`;
     - it also needs `backend.dlNoDel`, which a compacting image does not have.

**Who is affected:**
- items 15, 16, 18 and 21 (the walk's `:385`/`:388` and its `restoreImageM` construction);
- SNAPSHOT-SORRY #8, which rests on them.

**Restatement.**
- (a) Thread the records into the backend vocabulary in the drafted texts themselves:
  - `keyReadLocked`/`keyReadSnapC`/`keyCleanRead`/`isKeyBackendG` take `(r : CmpRecs)` with clause
    `□ (NC -∗ NC ∗ □ metaReadSpecR rt r Rd Tok)`, default `empty`;
  - `storeBackendT … r`;
  - `restoreView b γ RT q r m` over a given bucket `m`;
  - `Restore.specM` passes `r`.
  - Add the bridge law the walk needs: `keyCleanRead_of_backendC` (compacting, records `r` from
    `fkOpenD`, no `dlNoDel`).
- (b) Generalize `specR` over a bucket `m` with `bucketThinnedAt L' r.crev m`. Its post should give
  the index's state as "the log's index thinned at `r.crev`", say `idxThinAt γ.idx L' r.crev`. It
  needs a model lemma: an index rebuilt from a thinned bucket answers every read at `≥ r.crev` as
  the log's (`kiGet_avail`-style). The store's invariant in compaction mode must accept that state
  until the job's `treeIndex.Compact` runs.
- (c) Until (a) and (b) are drafted, hold items 15, 16, 18 and 21, as round 3 asked. The records
  part (`CmpRecs`, `crev`, `kbRecs`, `fkOpenD`) can be approved now.

### A2. `resumeCsM` requires the new backend's hook, which does not exist yet when `restore()` resumes the compaction

**Principles:** Complete ("each caller can establish the precondition"); Sound (faithful to what
the code runs).

**Evidence.**
- `resumeCsM d' γb' r P' f Pre Q Post`, on and resuming (mvcc R:398-402), is
  `kbHookIs (some d') γb' f ∗ csContract P' f Pre Q Post`.
- `kbHookIs (some d')` is `bkHookIs d'.γB f`: `f = #g`, `g ≠ func.nil`, `plHookRO d'.γB g`
  (`InvStore.lean:934-949`).
- `plHookRO` comes only from `SetTxPostLockInsideApplyHook`. In Go that call comes after
  `kv.Restore` (`server.go:1089-1093`); in the walk, `hSTP` (`:428`) comes after `hRst` (`:400`).
- So during `Restore`, the resumed `SetScheduledCompact`'s `LockInsideApply` (`store.go:38-42`)
  finds a nil hook and runs none (`batch_tx.go:113`).
- The backend's own spec has that arm: `f = func.nil ∗ (Pk ∗ Pre -∗ Q)`
  (`Spec/…/backend/batchTx__LockInsideApply.lean:34`). mvcc's real-backend hook vocabulary has no
  nil case.
- The resuming case is reachable in the 3-member cluster: a leader's snapshot taken while its
  compaction job runs has `sched > fin`.

**Who is affected:**
- items 15, 16 and 21 (the walk cannot supply `resumeCsM` when `r.resumes`);
- the store's write-session contract (`storeBackendT`'s `HF := hookFn γ`), which the resumed
  `updateCompactRev` uses.

**Restatement.**
- On and resuming, `resumeCsM` should state the unset hook, not a hook. For example: the client's
  half of the new backend's hook variable at nil (`backend.plHook d'.γB func.nil`, which the walk
  holds until `hSTP`), lent and returned, with the nil arm's contract
  `Pre ∗ (P' ∗ Pre -∗ Q) ∗ (Q ={⊤}=∗ P' ∗ Post)`.
- The bridge (`isKeyBackendG_of_backendC`) then needs the nil-hook branch of `LockInsideApply` at
  the store level. That is a new law, so add it to the list.
- If the server's batch-lock invariant cannot be kept without the hook, say what `Pre`/`Q` the walk
  passes. Uncertain: I did not check whether `batchLockInv` survives a write that skips the hook.
  The consistent index is not touched by it, since `SetBackend` reset it to 0 and
  `unsafeUpdateConsistentIndex` skips 0, `cindex.go:123-129`, `schema/cindex.go:69-73`.

## Second tier

### S1. Q7 (a) is decided but not drafted, and S1 of round 3 is now unblocked

`c`'s source at #8 (round 3's S1) was deferred to Q7. With Q7 (a) taken:
- define `crevOf`;
- hold the closer at `srvKVCloserM s E (crevOf A)` in `run`'s state;
- tie `keyImageM`'s `r.crev = crevOf A'`;
- add the scope premise where the request enters the log (above).

This is the apply side, outside this branch's scope, so at least name it in item 21 and add an item
for the scope premise.

### S2. The scheduler Draft: two conditions for the switch

1. **The payload must be pinned by `isFifo`.** In the Draft, `SchedNamesD` extends `SchedNames`.
   `Scheduler.Stop.specD` (`schedule/M2StorageDraft.lean:241-250`) takes
   `isFifo … γ.toSchedNames ∗ schedPay γ` for any `γ` extending them. A caller can pass `γ` with a
   fresh `pay` holding `True`, and then `Stop`'s proof cannot produce the context's real `PDone`.
   So as drafted, `Stop.specD` is unprovable. It becomes right only when `pay` is a field of
   `SchedNames`, so that `isFifo`/`fifoCtxDesc` fix it. The plan says this happens at the switch;
   item 19 should say it is required.
2. **`stopPayD γx` needs a home for `γx`** (mvcc R:680-682).
   - A job learns "some channel recorded at `γx` is `Done`".
   - To use it in `compactBarrier`'s `select`, it needs `dghostVar γx □ o.sstop` for the `o` it
     reads through `storeStopR`, and `schedPayIs γ.sch (stopPayD γx)`.
   - Neither is in `fieldShareAt`/`physOk`/`StoreObjs`.
   - Name it: a `PhysNames` field, which is fresh per scheduler, and `physOk`'s conjunct. It is
     internal, but it is an internal definition change, like item 26.

Good: the change is the least that carries the fact. Specifically:
- `jobFnSpecD_of`/`jobIsD_of` keep `run`'s jobs unchanged;
- `schedPay_elim` gives `▷ □ P`, and a job has a step for it;
- `schedDoneD_excl` makes the jobs' share sound;
- the exported `scheduler_fifo` reads the same.

### S3. Approved texts that exist only as prose patches over stale Lean

- Item 4/17: `store.Compact.specD` (Supply:196-217) still reads `storeStop s γ ∗ compactRight γ c`,
  and `compactJobPreD` (`:133-136`) still reads `storeStop ∗ schedLive`. The approved text is "the
  Lean, with item 17's prose substitution". The same holds for `updateCompactRev.specD` and
  `compactLockfree.specD`.
- Item 24 is prose only.
- Item 26 (`StoreNames.cm`) is not in Lean: the Drafts read `γ.kb`.

Each is a small edit. Draft them so that the user approves one text, and so that the proofs in
`M2StorageDraftSupply` show they compose.

### S4. Redundant conjuncts and a naming cost (clarity)

- `restoreImageM`'s and `keyImageM`'s `r.crev < L.length` follows from `recsOk L r`, since `crev` is
  a record or `-1`, and `|L| ≥ 2`. Drop it ("No constant or conjunct whose reason you do not know").
- `restoreImageM`'s on branch keeps `backend.fkV d'.γB true` beside `kbRecs`' `fkOpenD` on the same
  ghost name `γ.fkv`, at another type. At the switch they merge ("`fkV γ w` becomes `∃ n v, …`").
  State the merged text instead.
- `restoreRightPostM` is also `Close.specM`'s pre. It is the store's right to close by the mode, so
  call it that (`storeCloserM s γ c`). `restoreRightM` is then `storeCloserM` with, off,
  `crevFrozen ∗ ⌜c = -1⌝`. One vocabulary word fewer for D22's readers.

### S5. Round 3's second tier: status at `f3282099c3`

| Item | Status |
|---|---|
| S1 (`c`'s source) | Deferred to Q7; Q7 answered (a); not drafted (S1 above). |
| S2.1, S2.2 | Text only (S3 above). |
| S2.3 | Drafted (scheduler), with S2 above. |
| S2.4 | Done: `Close.specM` and the off law; Q3 correctly "does not dissolve". |
| S2.5 | Decided (`StoreNames.cm`), sound; not drafted. Item 25 follows (`isWatchableStore_withPhys` stays `rfl`; checked: the Draft's only mode reads are `wsFrozenM` and `crevRightM`, `M2StorageDraft.lean:84`, `:97`). |
| S2.6 | Done. |
| S3 | Q7, decided; placement above. |
| S4 | Done (`storeStopR s γ o`; `fieldShare_reclaim` without `curAt_agree`). |
| S5 | Done (`kbWTSupplyM_of_poolR`; item 21 states the `£ 1`). |
| S6 | Draft docstrings fixed; `InvStore`'s are left for the switch, as listed. Also stale: `Spec/…/store__restore.lean`'s "the trust boundary … not yet proved" header (it is proved: no `sorry`, linked `mvcc/Link.lean:118`). |
| S7 | Done. |

### S6. The approval list is not complete

Missing, beyond A1 and A2's own changes:
1. The backend vocabulary with records: `keyReadLocked`/`keyReadSnapC`/`keyCleanRead`/
   `isKeyBackendG`/`storeBackendT`/`restoreView` taking `r`. Item 18 says "switch-internal". It is
   not internal, because `keyCleanRead` and `storeBackendT` are in D22's `Restore.specM` and walk.
2. `keyCleanRead_of_backendC` (new exported bridge law, A1) and the nil-hook store law (A2).
3. The store invariant over an index rebuilt from a thinned bucket (internal; A1 (b)).
4. `γx`'s home (S2.2) and `isFifo` pinning `pay` (S2.1).
5. The Q7 scope premise (S1).

## Per target

**mvcc R** (`storeStopR`, `compactRightR`, `CmpRecs`, `kbRecs`, `fkOpenD`, `metaReadSpecR`,
`keyImageM`, `restoreImageM`, `resumeCsM`/`resumePostM`, both `Restore.specM`, `specR`, `revFinW`,
`resumeK`, `Close.specM`, `wsCloserR`)

Good:
- `CmpRecs.crev`/`resumes` match Go exactly, including the 0 corner.
- `kbRecs` is sound: `fkOpenD` is discarded, so it agrees, and it pins the open-time flag and bytes.
- `kbRecs_MW` closes round 3's F1.2.
- `resumeK` (continuation-passing) is a clean way to state "`restore()` calls `compactLockfree`",
  and `revFinW` mirrors Go's `found` branch.
- The jobs' share at fixed objects removes S4's risk by construction.
- The off laws are exact.

Findings: A1, A2, S3, S4.

**schedule Draft**

Good: minimal and sound in Go; no effect on `run` beyond `iprop(True)`.

Findings: S2.

**etcdserver R** (`srvWTStockInv`, `srvWTPoolR`, the take laws, `kbWTSupplyM_of_poolR`,
`srv_be_swapR`, `srvEnvOkD`, `srvKVCloserM`, `restorePre_of_applyM`, `snap_closer_after`,
`snap_supply_before`)

Good:
- the arithmetic checked;
- `restorePre_of_applyM` without the unfold of `isWatchableStore`;
- `snap_closer_after` composes in either mode.

Findings: S1 (via item 21), and A1/A2 through the walk.

**Step 1 Drafts** (mvcc `M2StorageDraft`, Supply, etcdserver `M2StorageDraft`, v3rpc, client,
cache, examples)

No churn: docstrings, the requested removal, and one new law. Findings: S3 (Supply's specs to
redraft for item 17).

**Switched internals:** unchanged since round 3, and correct. The docstrings saying "never in
compaction mode" are left for the switch (listed).

## Ranked by need of revision

1. **mvcc R's restore chain: `specR`, `Restore.specM` ×2, `restoreImageM`** (A1). Thread `r`
   through the backend vocabulary, generalize the bucket and the index, add the bridge law. Hold
   items 15, 16, 18 and 21.
2. **`resumeCsM`** (A2). Use the nil-hook arm.
3. **The approval list** (S6) and **Q7's placement** (S1).
4. **schedule Draft** (S2): pin `pay` in `isFifo`; give `γx` a home.
5. **Supply's compaction specs, as text** (S3, items 4/17/24/26).
6. **Clarity** (S4).
7. **Step 1's Drafts**: no change.
