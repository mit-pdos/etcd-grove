# R-A11-bbolt: re-review after the repairs (2026-11-09)

Reviewer: fresh and independent, read-only. Area A11: batch 4c (`SpecPlan/Spec/go_etcd_io/bbolt/`, `errors/`,
`examples/specreq/bbolt/`) and batch 4d (`internal/{common,freelist}/`, `examples/specreq/bboltinternal/`).
Base: `1aa6fc1337`. HEAD: `974e05095b`. Go: bbolt `743299d` (`.lake/src/bbolt`), etcd `a4d2bb17`.
OsFs: `GooseLang/Ext/OsFs/{Impl,Crash}.lean`. I wrote the verdicts below before I read
`repair-bbolt.md`. I read it afterwards only to check that findings N1-N4 are new (it does not
mention them).

## Verdicts

| batch | verdict |
|---|---|
| **4c** (bbolt API, internals, Options, errors) | **FAIL**: four new first-tier findings (N1-N4). Apart from those, it passes with the open decisions 4.1/4c-D1 (sector rule), C2 (`BoltSt.named`, chosen and awaiting confirmation) and the recorded OsFs `rename` gap (C42/C43). |
| **4d** (`internal/common`, `internal/freelist`) | **PASS**. Only `ReqWriteReload`'s Assumes changed (page size at most `2^16`), which closes the previous minor. |

## Original first-tier findings

| # | finding | status at HEAD | evidence |
|---|---|---|---|
| P-F1 / C2 | crash law false for a file created this generation | **Resolved, recorded as user decision C2** (option (ii)). It is consistent with OsFs; I tried to break it and could not (below). | `Model.lean` `BoltSt.named`, `fresh`, `recovers`; `Api.lean` `boltFresh_alloc`, `fileHolds_new` (`m.named = true`), `boltCrash` second disjunct; OsFs `OsCrash` (`Impl.lean:472-481`), `FileCrashed` (`Crash.lean:45,54`); `nonissues/bbolt-create-dir-not-synced.md` |
| P-F2 | `init`'s first write past the durable size | **Recorded open decision** 4.1/4c-D1, with the second clause added to the rule | `Api.lean` header, "The sector rule"; open-questions 4.1 |
| P-F3 | `fileHolds_new` lacks `m.hi = 0` | **Resolved** | `fileHolds_new.spec`: `m.size = 0 ∧ m.hi = 0 ∧ m.maps = ∅ ∧ m.named = true` |
| P-F4 / C-F2 | `openFileOk` persistent; `Open`'s error loses the file | **Resolved**: the contract is one-shot and carries `R`, which `Open`'s error returns. Whether `osFileOf` survives bbolt's `db.close()` is uncertain (os is provisional). | `Api.lean` `openFileOk`; `Open.lean` pre and post (`⌜o.openFile = func.nil⌝ ∨ R`) |
| P-F5 | commit and settle updates each consume the state | **Resolved** (nested `commitAU`); `boltState_commit_au` is provable as stated (sketch below). The new N3 is on the bbolt side of the same updates. | `Api.lean` `commitAU`, `boltState_commit_au`; `Tx__Commit.lean`; `DB__Update.lean` |
| P-F6 / C-F1 | no size law for read data | **Resolved** | `Model.lean` `Ent.wf`: `x.1.length ≤ maxKeySize`, `k.length + v.length ≤ bboltEntryMax` |
| P-F7 | no keyed-literal spec | **Resolved differently**: snippets build from `{}` plus field stores, and the backend's `boltOpenOptions` is its own assumed init. **However, the stores are not provable (N4).** | `Options.lean` header; `backend.go` `ReqBackendOpen`, `ReqDefrag` |
| P-F8 | `∗` between two restoring wands | **Resolved** (`∧`) | `Options.lean` `optsAt_bool/_int/_freelist/_openFile/_logger` |
| P-F9 | `physRep` has no laws; the write path does not close | **Partly resolved.** `Put`, `Delete`, `CreateBucket(IfNotExists)`, `Cursor.Delete`, `Set/NextSequence` close. The `rebalance`/`spill`/`allocate`/`write` chain closes at the stage level. **`DeleteBucket` does not close (N2), and neither does `Commit`'s `commitFreelist` error path (N3).** | `Internal.lean` rep laws; details below |
| P-F10 | `boltCrash` statement changes under option (b) | **Recorded** (4.1): the text now says so | `Api.lean` `boltCrash` docstring |
| C-F3 | no release law | **Resolved** (`boltRelease`). The reopen after the rename still has no source; it is part of the recorded OsFs `rename` gap, and the snippet's comment misstates it (see N5, second tier). | `Api.lean` `boltRelease.spec` |
| C-F4 | `Stats` after `Begin(true)` | **Resolved**: `statSlot (some (tx,T))` is any transaction's whole, plus `statSlot_wtx`. The backend's `backend__begin.lean:18` still says "until it lands" (stale comment, another area). | `Api.lean` `statSlot`, `statSlot_wtx` |
| C-F5 | backend `snapshot.WriteTo` fixes the bytes | **Resolved in 4a** (`beSnapN γ s I n`, fresh `bs` per call with `imgBytes I bs ∧ bs.length = n`) | `backend/snapshot__WriteTo.lean` |

## New first-tier findings

### N1. `Open`'s internal freelist commit is not in its spec; it falsifies `boltCrash` under `NoSync` and `boltRelease` after a failed sync (4c)

- **Go.** At the end of `Open`, this runs (`db.go:319-334`):

  ```go
  if !db.NoFreelistSync && !db.hasSyncedFreelist() {
      tx, txErr := db.Begin(true)
      if tx != nil {
          txErr = tx.Commit()
      }
      ...
  }
  ```

  It is a real commit: it writes a new freelist page and a meta at `txid+1`, with the same data.
  `db.NoSync` is already set (`db.go:191`), and `tx.write`/`writeMeta` skip `fdatasync` under it
  (`tx.go:572, 619`). `hasSyncedFreelist` is false for any file last written with
  `NoFreelistSync` (`db.go:473-474`), which is every etcd database.
- **Spec.** `Open.spec` takes no `boltState` and no update, so `σ` is unchanged. Its sketch does
  not mention this commit. `OptsM` does not track `NoFreelistSync`, and `OptsM.ok` admits every
  combination.
- **Run 1 (crash law).**
  1. `fileHolds_alloc` over an etcd-written file gives `σ = init D`, `dur = some []`.
  2. `Open` with `NoSync = true` and `NoFreelistSync = false`. The internal commit writes the
     freelist page and the new meta, and syncs neither.
  3. Crash. OsFs may keep the meta slot's new bytes and lose the freelist page; the sector rule
     even makes the new meta valid.
  4. The newest meta then points at a garbage freelist page. The next `Open`'s
     `freelist.Read`/`loadFreelist` fails or panics, and `fileHolds` ("a synced freelist page
     well-formed") does not hold.
  5. Yet `boltCrash` promises `fileHolds γ.path D`, since `σ.dur = some []`.
- **Run 2 (`boltRelease`, with `NoSync = false`).**
  1. The internal commit's `fdatasync` fails, either the data pages' or the meta's.
  2. `Open` returns its error and gives `boltClosed γ` back. `σ` is still `init D`.
  3. `boltRelease` promises every byte clean (`x.2 = true`, `lo = hi`). OsFs marks the failed
     writeback `lost` (`OsFile.syncFailed`, `Impl.lean`), so those bytes are not clean.
- **Callers.** Any client that opens an existing `NoFreelistSync` file with default freelist sync:
  `bbolt`/etcdutl tools, or a client switching modes. etcd itself (always `NoFreelistSync`), the
  bank (its file starts empty, so `init` writes a freelist) and `ReqDefrag` (a fresh file) do not
  reach it. The spec as stated admits it, so a client can derive a false durability claim.
- **Fix (one of):**
  - **(a), preferred.** `OptsM` gains `noFreelistSync`. When it is `false`, `Open` takes the
    client's update for this commit: a `commitAU γ D D o.noSync S`, data unchanged, so `dur`
    becomes `none` under `NoSync` and a failure sets `lost`. The error disjunct returns `S`'s
    outcome.
  - **(b), a scope restriction.** `OptsM.ok` requires `noFreelistSync = true ∨ noSync = false`,
    and `boltRelease`'s clean clause gets a premise that excludes an `Open` that failed after
    writing. (b) does not repair run 2 cleanly; (a) does.
  - Either way, `Open.lean`'s sketch must cover the internal commit.

### N2. `DeleteBucket`'s recursion cannot use `ForEachBucket.spec`: the callback changes the view (4c, F9 remainder)

- **Go** (`bucket.go:305-312`): `child.ForEachBucket(func(k) { return child.DeleteBucket(k) })`.
- **Spec.** `Bucket.ForEachBucket.spec` hands the callback `boltTx tx γ q T` and requires
  `boltTx tx γ q T` back, with the same `T`. The visited keys `ks` are fixed from `T.ents p`.
  The recursive `Bucket.DeleteBucket.spec` returns `boltTx tx γ 1 (T.dropBkt (p.child kb) k')`, so
  no instantiation closes. `DeleteBucket.lean`'s sketch ("the recursion, each nested bucket's
  `DeleteBucket` (its post `T'.dropBkt …`)") names no spec for this step.
- **Go also skips here.** Deleting while iterating skips a nested bucket when the child's leaf
  node is materialized (`issues/bbolt-deletebucket-nested-leak.md`, etcd-io/bbolt#1305). The
  iteration does not even visit every element of `ks`. This is harmless to the view, because the
  whole child is removed by `node.del` and `dropBkt` resets the generations below.
- **Callers.** `Tx.DeleteBucket` / `Bucket.DeleteBucket` success arm. That covers etcd's
  `UnsafeDeleteBucket` (`ReqDeleteBucketNotFound`'s success case) and `ReqNested`'s final
  `DeleteBucket`.
- **Fix.** An internal spec of `ForEachBucket` for this use. The callback gets and returns
  `boltTx tx γ 1 T_i` with `T_i` any view that differs from `T` only at or below `p` (an `I i T_i`
  loop state). It is called on some subsequence of `ks`, and the post is `∃ T', I _ T'`.
  `DeleteBucket`'s sketch then needs only that the child is gone after `node.del`, which
  `physRep_delBkt` gives from `bktDropped`.

### N3. `Commit`'s `commitFreelist` error path: the callee releases `rwlock` before `Commit` can fire `commitAU` (4c)

- **Go.** On an allocation error, `tx.commitFreelist()` calls `tx.rollback()` itself
  (`tx.go:285-293`). That runs `tx.close()`, which unlocks `rwlock` (`tx.go:364-365`). `Commit`
  then just returns `err` (`tx.go:218-222`).
- **Spec.** `Tx.commitFreelist.spec`'s error post is `txDone tx`, so the updates are still unfired
  at that point. Firing them later is unsound:
  - The outer update's post demands `⌜σ.data = B⌝`. After `rwlock` is released, another writer
    may begin and commit (its own `commitAU` from the client's invariant), so `σ.data ≠ B`.
  - A late settling update sets `busy := false` while that other writer's meta write may be in
    flight. A concurrent successful `DB.Sync` then sets `dur := some []` for data whose meta is not
    durable. The `busy` flag exists to block exactly this.
  - All the other error paths (`spill`, `grow`, `write`, `writeMeta`) roll back in `Commit`'s own
    body, where the updates can fire first. `Tx.Commit.lean`'s sketch ("every error path fires
    both updates then `rollback`") does not hold for this one.
- **Reachable?** Not with `NoFreelistSync` (etcd). Yes for the bank and every default-options
  client, when `db.allocate` fails: an `mmap` errno on remap, or `MaxSize`.
- **Fix.** Either:
  - `Tx.commitFreelist.spec` takes the `commitAU` (pre) and, on error, returns
    `txDone tx ∗ ∃ ok synced failed brk, S ok synced failed brk` (fired before its `rollback`;
    the success arm gives the update back); or
  - its error post returns the transaction before rollback (`wtxAt … spilled`) and `Commit` calls
    the rollback, which needs a fork change.

  The first is a spec-only fix.

### N4. The `optsAt` field laws give no way to store a field: `dq'` is unconstrained (4c; the snippets F7 now relies on)

- **Evidence.** In `optsAt_bool/_int/_openFile/_logger/_freelist` (`Options.lean`), the field's
  points-to is `↦{dq'}` with `∃ dq'` and no relation to `dq`. A Go store needs the full points-to
  `↦`. The "store" branch (`⌜dq = DFrac.own 1⌝ -∗ ∀ y, … ↦{dq'} y -∗ …`) is unusable unless the
  client knows `dq' = own 1`, and nothing says so.
- **Callers.** `ReqBackendOpen` (`opts.MmapFlags = …`, `opts.NoFreelistSync = true`,
  `opts.NoSync = …`), `ReqDefrag` (`opts.OpenFile = …`, `opts.NoSync = true`, …), and etcd's
  `newBackend`/`createDefragTmpDB` field stores. The F7 resolution routes all of these through
  stores, so they do not close.
- **Fix.** Add `⌜dq' = dq⌝` to each field law (or drop `dq'` and use `dq`). This is true of the
  intended realization: the struct's points-to at `dq` gives each field at `dq`. The old
  `specs-ref` statement may have had the same defect.

## Second tier

- **N5 (`ReqDefrag`'s reopen).**
  - The snippet calls `os.Rename(tdbp, path)` and then `bolt.Open(path, …)` with no directory
    sync. Its Specs comment says the copy meets "fileHolds_image's premise once its name is made
    durable by the rename's directory sync", but there is no such sync in the code (nor in etcd's
    `finishDefrag`). So `fileHolds_image`'s `m.named = true` has no source.
  - `boltRelease`'s image clause also needs `σ.data ≠ Data.empty`, so an empty source database
    gives no image at all.
  - This sits inside the recorded OsFs `rename` gap (C42/C43, open-questions 920-965). Correct the
    comment, and either add "the source holds a bucket" to Assumes or give `boltRelease` an
    init'd-empty image case.
- **N6.** `statSlot (some (tx, T))` does not tie `tx` to the `db` whose `statlock` it pays for (no
  `txDB tx db`). A transaction of a reopened database (same `γ`) could pay for an old, closed
  `*DB`'s `Stats`. It is realizable but contrived. Add `txDB tx db` to `DB.Stats`' pre in the
  `some` case.
- **N7.** `node.put`'s premise `uint.nat pg < uint.nat C.hwm`, with `pg = 0` from `Put` and
  `CreateBucket`, needs `0 < C.hwm`. No stated law gives it; it comes only from unfolding
  `wtxCore`'s realization. Add `2 ≤ uint.nat C.hwm` to `physRep_meta` or to a `wtxCore` law.
- **N8.** `ReqBackendBatch`'s `tx.CreateBucketIfNotExists(keyBucket)` needs "the root has no value
  at `keyBucket`", which is not in its Assumes (carried over from the previous round).

## Crash-schedule attacks on `named` / `boltFresh_alloc` / `boltRelease` (none breaks the law, except N1)

I tried these against OsFs's `OsCrash`/`CrashImage`/`FileCrashed`:

- **Created file vanishes after a synced commit** (`named = false`): `recovers Data.empty` and the
  `osMeta … none` disjunct. Covered.
- **Created file survives empty, with zero metas, or with a partial `init`**: `fileHolds`'
  "empty / init redoes, `D = Data.empty`" case. `recovers` admits empty while `named = false`.
  Covered. With `named = true` (from `fileHolds_new`), `σ.data` is empty until the first commit.
  Covered.
- **`boltFresh_alloc` over an empty file whose OsFs name is in fact durable**: conservative. Fine.
- **A surviving file in the next generation**: `OsFile.ofDisk` sets `named := true`, so
  `fileHolds`' "name too" holds.
- **The `named` / `lost` / `busy` interplay**:
  - A failed `DB.Sync` before or during a commit: `lost` gives `dur := none` at the commit update,
    or keeps `dur` at the settle.
  - `DB.Sync` against a `NoSync` commit: under OsFs's atomic `fdatasync`, `busy` blocks it while
    the meta is in flight, and after the settle the sync is genuinely complete.
  - All safe in the model.
- **`boltRelease` with `dur = some []` and `lost = true`**: reachable only after a failed sync with
  no dirty bytes (a commit's failure gives `dur ≠ some []`), so the bytes are clean. **The
  exception is N1 run 2.**
- **Two names on one path in defrag** (`γ_old` released, `γ'` allocated): `boltRelease` consumes
  `boltState γ 1`, so `boltCrash` cannot be applied to the released name.

## Proof plans of the changed specs (summary)

- **`Bucket.Put`** (closes): `Cursor` and `seek` give `curPath … (.inr kb)` and `seekRaw`; the
  flag check; `wtxCore_view` gives `wtxCore C ∗ physRep T C`; `Cursor.node` gives `keyLeaf C' p kb
  n` (using `physRep_meta`'s `T.gen = C.gen`) and `repKept`; `node.put` (`pg = 0`: N7); then
  `physRep_set` with `newEnt 0 vb (val vb)`, the bounds from the checks and the pre; back to
  `boltTx` by `wtxCore_view`.
- **`Bucket.Delete`, `Cursor.Delete`**: the same steps with `physRep_del`. At past-the-end,
  `node.del(nil)` is a no-op by `wtxCore_keys`. Closes.
- **`Bucket.CreateBucket(IfNotExists)`, `Tx.CreateBucket`**: `Bucket.write` (fresh) gives
  `emptyBktVal`, then `physRep_set` with `newEnt bucketLeafFlag`, then `Bucket.Bucket` at the new
  view. Closes.
- **`Set/NextSequence`**: `Bucket.node(root, nil)` gives `roots b`, then `wtxCore_seq`. Closes.
- **`DeleteBucket`**: N2.
- **`Tx.Commit`**: `rebalance` → `spill` (with `node.spill`, `Tx.allocate`'s `bufs`/`freshPage`,
  `wtxCore_buf`, `node.write`'s `nodeWritable`) → `Free` → `commitFreelist` (N3 on its error) →
  `grow` → `write` → `writeMeta` (`Q :=` the inner update) → inner update → `close`. The stage
  predicates (`wtxAt`) are the package's own realization. Closes except N3.
- **`boltState_commit_au`**: from `boltState γ 1 σ`, the outer update gives `σ`. At COMM the
  client receives `⌜σ.data = B⌝ ∗ boltState (σ.commit/attempt)` and builds the inner update from
  that copy. The inner COMM yields `S`, which carries the remembered `σ.data = B`. Closes.
- **`DB.Update`**: as before, with `commitAU` from the callback. `T.managed` is reset internally.
  Closes given `Commit`.
- **`Open`**: closes with the one-shot `openFileOk` (R back on error), **except N1**.
- **`DB.Stats`**: closes (N6 minor).
- **`Bucket.free`, `node.free`, `node.rebalance`, `node.spill`, `Bucket.node`, `Tx/DB.allocate`**:
  `repKept` posts are consistent with a realization of `physRep` over the node cache, the
  buffers and the snapshot.

## Snippets (changed or added)

| snippet | verdict |
|---|---|
| `ReqBackendOpen` | **no** (N4: field stores). Otherwise `optsAlloc`, `Open`. |
| `ReqBackendBatch` | **yes**, minor N8. `Stats` via `statSlot_wtx`; `commitAU` from `boltState_commit_au`. |
| `ReqBackendRead` | **yes**. The Assumes now has the writer's bounds and the invariant. |
| `ReqDefrag` | **no**: N4 for the stores; reopen per N5 (recorded `rename` gap). Otherwise it closes: one-shot `OpenFile` and the `R` error path through `boltRelease`; `Ent.wf` bounds for `CreateBucketIfNotExists`/`Put`; `putLoan` across the copy's commit and then the source's `Rollback`; `dbBroken_state`; the `Sync` update giving `dur = some []`; the double `Close`. |
| `ReqDeleteReturned` (new) | **yes**. Keys through `txBytes_acc` against `txLive` shares while `Delete` holds all of `boltTx`; then `Get` nil by the view. Covers the completeness reviewer's S1. |
| `ReqCrashAtomicDurable` | **yes, pending 4c-D1** (the file pre-exists with a durable name, via `fileHolds_new`; C2). |
| `ReqNested` | **yes** for the Assumes. Its final `DeleteBucket` inherits N2 (the spec is fine; its proof does not close). |
| `ReqWriteReload` (4d) | **yes**. |

## Bugs in the Go code

None new. N1-N3 are spec defects, not bbolt bugs: `NoSync`'s possible corruption is documented
(`db.go:45-50`). N2 touches the known `issues/bbolt-deletebucket-nested-leak.md`. I filed nothing:
this round is read-only.

## Counts

- Spec files changed since `1aa6fc1337` in the area: 27 (all in `bbolt/`; none in `common/`,
  `freelist/`, `errors/`). I re-planned 20 of them; the rest are comment-only changes. 4d's 144
  are unchanged and still pass.
- Laws: 10 new or changed (`commitAU`'s `boltState_commit_au`, `statSlot_wtx`, `fileHolds_new`,
  `boltFresh_alloc`, `boltRelease`, `boltCrash`, `physRep_meta/_set/_del/_delBkt`, `wtxCore_buf`,
  `wtxCore_seq`, the five `optsAt` field laws). Plausible: all but the `optsAt` field laws, which
  are true but too weak to use (N4), and `boltRelease`/`boltCrash`, which are false in N1's runs.
- Snippets changed or added: 8. Provable: 5 (`ReqBackendBatch`, `ReqBackendRead`,
  `ReqDeleteReturned`, `ReqCrashAtomicDurable` pending 4c-D1, `ReqWriteReload`), plus `ReqNested`
  at spec level. Not provable: `ReqBackendOpen`, `ReqDefrag`.
- Original first-tier findings: 14 (provability F1-F10, completeness F1-F5, with duplicates
  merged into 13 rows). Resolved: 9. Resolved differently: 1 (F7, with N4 left behind). Recorded
  open: 3 (F2, F10, plus C2 for F1). Partly resolved: 1 (F9: N2, N3).
- New first-tier findings: 4 (N1-N4). Second tier: 4 (N5-N8).
