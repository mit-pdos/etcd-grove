# RR: recheck of R-A5 N1 (raftlog snippets) and R-A11 N1-N5 (bbolt) (2026-11-09)

Reviewer: fresh and independent, read-only. Base `4a6a9b6b6e`, working tree at review time (the fixes
are uncommitted). Go: `.lake/src/{raft,bbolt,server}`. I wrote the verdicts below before I read the
"Re-review" sections of `repair-raft-core.md` and `repair-bbolt.md`. Afterwards I read those sections
and found nothing that changes a verdict. They state that etcd passes `emp` to `Open`, which is
exactly where the regression NR2 sits.

`etc/lean-check.py` passes (0 errors) on `bbolt/{Open,Bucket__ForEachBucket,Tx__commitFreelist,Options}`
and `raft/v3/raft__hasUnappliedConfChanges`.

## Verdicts

| batch | verdict | why |
|---|---|---|
| **R3** (raftlog snippets) | **FAIL** (one Assumes line) | N1(a) and N1(b) are fixed. `ReqCompactApplied` still lacks `applied ≥ base`. Its new comment claims `term(i)` answers when `compactFloor` is the base, which is false when `base > applied` (NR1). |
| **4c** (bbolt) | **FAIL** (one line, in another area's file) | N1-N4 are fixed in bbolt, and N5 is fixed as far as it can be without the OsFs rename rule. N1's fix makes `OptsM.dflt.noFreelistSync = false`. The backend's assumed `boltOpenOptions_init` is written as `{ OptsM.dflt with mmapFlags := … }`, so it now says `NoFreelistSync` is off. Go's literal sets it on, so the fact is false of Go, and etcd's `New`/`Defrag` must now supply an update they do not have (NR2). Otherwise this would be PASS WITH OPEN DECISIONS: 4c-D1, C2, C42/C43, and the second spec `ForEachBucket.spec_del` (below). |

## Findings table

| # | finding | status | evidence |
|---|---|---|---|
| R-A5 N1(a) | `floor ≤ applied` missing from `ReqScanConfChanges`, `ReqCompactApplied` | **Resolved** for `ReqScanConfChanges`: with "applied ≥ base", `compactFloor = max base (max applied floor) = applied < applied+1`, which is `scan.spec`'s premise (`raftLog__scan.lean:41`). This matches R2's `hasUnappliedConfChanges` premise, now `compactFloor ≤ applied`. **Not fully resolved for `ReqCompactApplied`**: NR1. | `reads.go:89-91`; `ready.go:72-76`; `ApiLog.lean:285` |
| R-A5 N1(b) | `cs` full for `CreateSnapshot` | **Resolved** in both snippets. Second tier: `ReqCompactApplied`'s laws line still omits `raftLog_publish`/`logFloor_stored`, both of which `logStor_createSnapshot` needs (`logStored`). `ReqMoveBeforeAdvance` lists them. | `ready.go:74-78, 101-108` |
| R-A11 N1 | `Open`'s internal freelist commit not in the spec | **Resolved in bbolt; introduced NR2 in the backend.** | below |
| R-A11 N2 | `DeleteBucket`'s recursion vs `ForEachBucket.spec` | **Resolved** (`spec_del`, `TxView.sameAt`). Open decision: a second spec of one function. Second tier: the `txBytes`→`key ↦*` step. | below |
| R-A11 N3 | `commitFreelist`'s rollback before the updates fire | **Resolved** | `Tx__commitFreelist.lean` spec; `tx.go:285-293` |
| R-A11 N4 | field laws at an unrelated `dq'` | **Resolved**: every one of the five laws now gives the field at `dq`. A store at `own 1` now has a source. `ReqBackendOpen`/`ReqDefrag` store at `optsAlloc`'s `own 1`. | `Options.lean:116-166` |
| R-A11 N5 (2nd tier) | `ReqDefrag`'s reopen; empty source | **Partly resolved, as recorded.** The comment is corrected. Assumes adds "at least one bucket", so the copy's `σ.data ≠ empty` and `boltRelease`'s image clause applies. The reopen remains the recorded OsFs rename gap (C42/C43). | `backend.go:246-266` |
| R-A11 N6-N8 | | **Resolved.** `DB.Stats` takes `txDB tx db`, which `Tx.DB`/`Begin` give. `wtxCore_hwm` (`2 ≤ hwm`) holds: `init` writes 4 pages. N8's Assumes line is added. | |

### R-A11 N1, checked in detail

- **What the spec says now.** With `noFreelistSync = false`, `Open.spec` takes
  `∀ D, commitAU γ D D o.noSync Sf`. On success it returns `Sf true (!ns) false false` or the update
  back. On error it returns some `Sf …` or the update back.
- **It closes against the specs:**
  1. `DB.Begin(true)` gives `∃ D, boltTx tx γ 1 (TxView.wr D false ns) ∗ txLive tx 1`
     (`DB__Begin.lean:61-62`), with `ns` = `o.noSync` from `isBolt`. That is why the pre binds
     `∀ D`.
  2. `Tx.Commit.spec` takes `commitAU γ T.base T.cur T.noSync S`, which here is
     `commitAU γ D D ns Sf`. On success it gives `S true (!ns) false false`.
  3. On error, `txDone ∗ ∃…, S …`, then `DB.Close` with `boltOpened`, which gives `boltClosed`.
  4. A `Begin` error leaves the update unfired, which the post's second disjunct returns.
- **Crash schedules against the new update** (OsFs `OsCrash`, sector rule 4c-D1). I tried each of
  these; none breaks `boltCrash` or `boltRelease`:
  - **`NoSync`, crash after the freelist and data `pwrite`s, before the meta write.** The update
    has not fired, so `dur = some []`. The written pages are free in the current meta, and the meta
    slot written is the older one (`txid+1 % 2`). Every crash image's newest valid meta is the
    current, synced one, so `fileHolds D` holds.
  - **`NoSync`, crash after the meta `pwrite`** (new meta valid, freelist page lost: R-A11's
    run 1). The commit update fired at the meta write, and `BoltSt.commit … ns=true` gives
    `dur = none`. `boltCrash` needs `σ.dur = some _`, so it promises nothing. **Fixed.**
  - **Sync on, `tx.write`'s `fdatasync` fails** (R-A11's run 2).
    1. The commit update fires with `ok = false`: `attempt` gives `dur = some [D]`.
    2. The settle fires with `failed = true`: `lost`, and `dur` stays `some [D]`.
    3. `Close`, error.
    4. `boltRelease`'s clean clause needs `dur = some []`, so it does not apply. **Fixed.**
    5. The same holds when the meta's `fdatasync` fails: `commit` gives `dur = some [D]`, then
       `lost`.
  - **Sync on, crash between the meta `pwrite` and its sync.** `dur = some [D]`, `busy`. Either meta
    survives, and the new one's freelist page was synced by `tx.write`. Both hold `D`.
  - **`grow`'s `file.Sync` fails** (`NoGrowSync` off): `failed`, `lost`. Covered.
  - **Initialized file** (`hasSyncedFreelist` true after `init`): no commit, so the update comes
    back. Covered.
- **Second tier.** A client that holds `boltState γ 1 σ` locally (not in an invariant) and gets the
  update back unfired cannot recover `boltState` without firing it. Firing it with `ok = false` at
  `D = σ.data` costs `dur` (`some [data]`, or `none` under `NoSync`) until a `DB.Sync`. A
  cancelable invariant around the state avoids this. No current caller is affected: the bank's state
  is in an invariant, and etcd and defrag pass `emp`. Consider saying so in `Open.lean`'s header.

### R-A11 N2, checked in detail

- **The recursion closes.**
  - At `i = 0` the callback's view is `T` itself: `sameAt T T p` holds by `bktH_live` with
    `s, es` taken as `p`'s own.
  - The child's `bktH` is persistent and stays current. `sameAt` keeps the generations of `p` and
    above, so `T'.gens p = gs`.
  - `DeleteBucket` chooses `I i T' := ∀ j ≥ i, ks[j] is a bucket at p in T'.cur`. Each callback
    succeeds: no `ErrBucketNotFound`/`ErrIncompatibleValue`.
  - The callback's post `T'.dropBkt p kb` is `sameAt T _ p`: its data is `T.cur.modAt p (bkt s es')`,
    and its generations change only strictly below `p`.
  - `I (j+1)` holds because keys are distinct.
- **The final view.** Two views that are `sameAt` the child `q = pOuter.child kb` have equal
  `dropBkt pOuter kb` (`Model.lean:219-222`):
  - at `q` both give `T.gen q + 1`;
  - strictly below `q` both give `0`;
  - elsewhere the generations are equal;
  - the data removes `q` whole.

  So the outer post `T.dropBkt p kb` follows.
- **Go's skip** (`bucket.go:604`, etcd-io/bbolt#1305): the cursor yields an increasing subsequence
  of `ks`. A key yielded from a stale page is one not yet deleted. This matches `spec_del`.
- **Open decision.** `spec_del` is a second proved spec of one function, which goes against
  PRINCIPLES "One spec per function" (a hard rule: "A step that would start a family goes to the
  user first"). The file records it as a margin, but it is not in `open-questions.md`. Either put
  it to the user, or make one spec that covers both: at fraction `q`, with the view allowed to change
  only when `q = 1`, as a gated row.
- **Second tier: the key bytes.** `spec_del`'s callback gets `txBytes tx γ k kb`, but
  `DeleteBucket.spec` needs `key ↦*{dk} kb`. The only stated law, `txBytes_acc`, needs a `txLive`
  share, and `DeleteBucket` holds none. The step needs a realization fact, or the internal spec
  should hand the callback `∃ dq, k ↦*{dq} kb` (given back). This is uncertain: bbolt's own proof may
  unfold `boltTx`.

### R-A11 N3, checked in detail

- **Go** (`tx.go:285-293`): the allocation error runs `tx.rollback()` inside `commitFreelist`.
  `Commit` returns at once (`tx.go:218-222`).
- **Spec.** It fires both updates before that rollback, while the writer holds `rwlock`, so
  `σ.data = T.base` holds.
  - `failed = false` is right: `db.allocate`'s remap (`db.go:1278-`) does no `fsync`.
  - `brk` follows the mapping state, as for `spill`'s error (pre-existing).
  - The success arm returns the update unfired.
- **`Commit`'s plan:** `commitFreelist`'s error arm gives `txDone ∗ ∃…, S …`, which is
  `Commit.spec`'s error post.

## New first-tier findings

### NR1 (R3). `ReqCompactApplied` lacks `applied ≥ base`; its new comment's "compactFloor is … the base and term(i) answers" is false

- **Go.** `raftLog.term` (`log.go:398-400`) returns `ErrCompacted` when `i+1 < firstIndex()`. With
  no snapshot pending, `firstIndex()` is the storage's, at least `base + 1`. So `term(applied)`
  answers `ErrCompacted` whenever `applied < base`, and the snippet panics
  ("compacted past the floor").
- **Spec.**
  - `term.spec` admits it: `i < compactFloor`, with `compactFloor = base` (`raftLog__term.lean:50`,
    `ApiLog.lean:285`).
  - `Wf` bounds `base ≤ committed`, not `base ≤ applied` (`ApiLog.lean:416`).
  - "No snapshot pending" (`us.snap = none`) does not exclude it. After `restore` and
    `stableSnapTo` the snapshot is no longer pending, but `applied` lags `base` until `appliedSnap`.
    These are separate steps (`MsgStorageAppendResp` / `MsgStorageApplyResp`; separate in time
    under async storage writes).
  - "i published by raft" does not exclude it either: the publication's `freezeStable i` needs
    `base ≤ i` only when it is made, and a later `restore` raises `base`.
- **Fix.** Add "applied ≥ the log's base (outside appliedSnap)" to `ReqCompactApplied`'s Assumes,
  as `ReqScanConfChanges` has it. Reword "compactFloor is the applied index or the base" to
  "compactFloor is the applied index". Also add `raftLog_publish.spec, logFloor_stored.spec` to its
  laws line.

### NR2 (4c regression, in `storage/backend`). `boltOpenOptions_init` now states `NoFreelistSync` off

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/backend/Durable.lean:142-145` assumes
  `optsAt l DFrac.discard { Bbolt.OptsM.dflt with mmapFlags := W64 Bbolt.mapPopulate }`. N1 added
  `noFreelistSync := false` to `OptsM.dflt` (`Model.lean:324-327`), and `optsAt_bool` now tracks the
  field.
- **Go.** `config_linux.go:29-32` is `&bolt.Options{MmapFlags: syscall.MAP_POPULATE,
  NoFreelistSync: true}`. The assumed fact is now false of Go: `optsAt_bool "NoFreelistSync"` gives
  a points-to of `false` where the heap holds `true`. Its docstring ("`NoFreelistSync` is not
  tracked by 4c's `OptsM`") is now stale.
- **Callers affected:**
  - `New.spec` (`newBackend`: `*bopts = *boltOpenOptions`, `backend.go:216-233`): `Open`'s pre now
    demands `∀ D, commitAU …`, which `New`'s proof has no source for (its sketch builds no update).
  - `Defrag`'s reopen `bolt.Open(dbp, …, b.bopts)` (`backend.go:594`).
  - `createDefragTmpDB` (`options := *b.bopts`, `backend.go:521-534`).

  The repair note says that etcd passes `emp`. That is true of Go and of the `ReqBackendOpen` snippet,
  which stores the field explicitly, but not of the backend's spec.
- **Fix.** `{ Bbolt.OptsM.dflt with mmapFlags := W64 Bbolt.mapPopulate, noFreelistSync := true }`,
  and update the docstring. Then `Open`'s `emp` branch applies to etcd's `New`, `Defrag` and the temp
  database.

## Regressions checked (diff `4a6a9b6b6e`)

- **bbolt**, every changed file:
  - **`Model`**: the `OptsM` field; `dflt` matches `DefaultOptions`, `db.go:1483-1487`.
  - **`Options`**: the field laws, with `NoFreelistSync` tracked.
  - **`Open`**, **`Tx.Commit`** (sketch only) and **`commitFreelist`**: as above.
  - **`ForEachBucket`/`Internal`** (`sameAt`, `wtxCore_hwm`), **`DeleteBucket`** (sketch) and
    **`DB.Stats`**.
  - No other regression in the area. **NR2 is the regression outside it.**
- **Snippets:**
  - `bank.go`: the default options are off, and the update comes from its invariant (an `Sf`
    independent of `D` is buildable from `boltState_commit_au` plus AU monotonicity, since the
    commit gives `σ.data = D`).
  - `backend.go`: N5/N8 Assumes.
  - `backend/snapshot.go` (another area's N3, `writeDurable` with file and directory `fsync`): it
    looks right, but I did not check it against OsFs's (assumed) directory sync.
- **raftlog/raft**:
  - The two Assumes edits.
  - `hasUnappliedConfChanges`' premise is `compactFloor ≤ applied`. This is consistent with
    `ReqScanConfChanges`.
  - The other raft edits are R-A4's (`raftState_crash`'s `j = b.ents.length`, `logStored_mono` and
    `logFloor_mono`, docstrings). They are plausible and outside this recheck.

## Bugs in the Go code

None found.

## Counts

- **Rechecked:** 2 + 5 findings (plus N6-N8). Resolved: 6. Partly resolved: R-A5 N1 (NR1) and
  R-A11 N5 (recorded gap).
- **New first-tier findings:** 2 (NR1, NR2). Each is a one-line fix.
- **New second-tier findings:** 3:
  - `ReqCompactApplied`'s laws line;
  - an unfired `Open` update and a locally held state;
  - `spec_del`'s `txBytes`→`↦*`.
- **Open decision:** 1 (`ForEachBucket.spec_del` as a second spec).
