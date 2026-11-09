# R-A10 (storage: mvcc core and watch, adt, backend, schema, pkg leaves): re-review after the repairs

Reviewer: independent, read-only. Commit under review: `974e05095b` (HEAD), against the verify round's
`1aa6fc1337`. Reports re-checked: `A10-storage-provability.md` and `A10-storage-completeness.md`. I
checked each finding against the spec text and the pinned Go (`.lake/src/server/storage/...`). I wrote
the verdicts below before reading the repair reports. Afterwards I read only `open-questions.md`, to
name the decisions that are recorded.

## Verdicts

| batch | verdict | open decisions |
|---|---|---|
| **3e** mvcc core | **PASS WITH OPEN DECISIONS** | A8 (hashing excludes `Restore`: `KV.Restore.contract`'s whole gate; C46 states it as a scope until decided) |
| **3f** mvcc watch, adt | **PASS WITH OPEN DECISIONS** | the watch id fixed at `0` (`issues/etcd-watch-id-reuse-stale-events.md`, `batch-2b.md`); A9 (reader tokens) |
| **4a** backend (`MvccStorage`, `Durable`, `LeaseBackend`, `AuthBackend`, `SchemaTx`) | **PASS WITH OPEN DECISIONS** | C42 (`beCrash`'s revert case: it can only be realized once OsFs has `rename` and a crash case that brings back an unsynced rename's old entry); `ReqSnapshotFresh`'s assumed `os.WriteFile` (open-questions, "`os.WriteFile` is assumed") |
| **4b** schema, pkg leaves | **PASS WITH OPEN DECISIONS** | 3.15 (`GracefulClose` against the snapshot sender's concurrent `ReadAll`) |

No new first-tier finding.

## The original first-tier findings

| # | finding | status at HEAD | evidence |
|---|---|---|---|
| B1 | `keyBackend_intro`'s lock rows and its way back do not close (`kbData`'s parked case cannot be refuted) | **Resolved** | See "B1" below. |
| B2 | `beCrash` concludes at the crashed generation's heap | **Resolved** | `Durable.lean:146-148`: the conclusion is now `@beFile _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p o` and `@beNoRevert … ⟨…, L'⟩`, the heap `Bbolt.boltCrash.spec` uses (`bbolt/Api.lean:637`). The header's step-1 text is updated (`:41-47`). The `rv = some o0` case is new. It rests on OsFs's missing rename crash relation: open decision C42. |
| B3 | `ReqDeleteVisible` is false in Go (read through a `ConcurrentReadTx`) | **Resolved** | `parts.go:84-96` now reads through `be.ReadTx()` with `RLock`/`RUnlock`. In Go, the deleting session's `Unlock` commits (`batch_tx.go:355`), and `unsafeCommit` resets the read buffer and begins a fresh read transaction. `readTx.UnsafeRange`'s single-key case is then exact (`rdRange`, `es = nil`, limit 1, `read_tx.go:79-82`). The cited nonissue path is correct (`nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`). |
| W1 | no law excludes `wsClosed` while `wsOpen` is held | **Resolved** | `ApiWatch.lean:370-374`: `wsOpen_closed.spec : wsOpen ι ∗ wsClosed ι ⊢ False`. The intended realization is stated (`:80-83`: a ghost variable owned whole, which `Close` discards). Each `mvccwatch` snippet that calls `Watch` now cites it. The `Watch` triple is unchanged, and that is right: v3rpc's `recvLoop` races `sws.close()`, so the triple must not take `wsOpen`. |
| F1 | `backend.Snapshot`'s post ("some committed image") is too weak for the merged snapshot | **Resolved** | See "F1" below. |
| F2 | `examples/mvccrand`'s boot is not served (no `meta` bucket before `mvcc.New`) | **Resolved** (a second-tier text gap remains: N1) | See "F2" below. |

The second-tier findings of the two reports:
- **S1** (`readTx`/`baseReadTx.UnsafeRange` admitted a duplicate entry): resolved. The hook clause is now waived only for `es = slice.nil` (`readTx__UnsafeRange.lean:59`, `baseReadTx__UnsafeRange.lean:34`), which matches `read_tx.go:79-82`.
- **S2** (`recvEvents`): resolved (`history.go:42-46` skips a `-1` response).
- **S3** (`ReqSeqRange`): resolved (`ranges.go:18`, `b < end`).
- **S4** (stale names in `MvccStorage.lean`): resolved (`leaseHookRun_intro`; the conversion is now called "the hook conversion, a conjunct of the post").
- **Completeness S1-S4**: S3 and S4 are recorded in open-questions. S1 and S2 were not re-checked, since they are outside this area's files.

### B1

`beTurn γ` is a new exclusive, timeless predicate (`Api.lean:424-425`), with the laws `beTurn_excl` and
`beTurn_timeless` (`:729-732`).
- Every `Lock*` triple returns it: `batchTx{,Buffered}.{Lock,LockInsideApply,LockOutsideApply}`, and `SchemaTx`'s `btLockIn`/`btLockOut`/`btSectOut`.
- `batchTxBuffered.Unlock`'s second atomic update takes it back (`batchTxBuffered__Unlock.lean:72`, also `SchemaTx.lean:359`).

The bridge parks the turn with `lockTok γB` in `kbData`'s parked case (`MvccStorage.lean:35-41`).

Plan for the lock row:
1. `LockOutsideApply` returns `beTurn`.
2. Opening `kbObs`'s update gives `kbData`. Its parked case holds a second `beTurn`, which `beTurn_excl` refutes. So the bridge takes `beCur` from the batch case and leaves `lockTok ∗ beTurn` in its place.
3. At `Unlock`'s second update, the bridge's view of mvcc's update finds `kbData` parked and hands its `beTurn` to the backend's update. It puts `beCur` back from the frame, so `kbData` returns to the batch case.

This is true of the Go:
- The turn returns to the lock's invariant before the mutex is released. The second update fires either at the commit (`batch_tx.go:355`) or right after the first update, and both happen before `t.batchTx.Unlock()` (`:358`).
- Internal sessions (`Commit`, `Defrag`, `CommitAndStop`) take the turn from the lock's invariant themselves.
- No client holds two sessions.

No other caller of `Unlock`'s two-update form is affected:
- the pre-commit hooks' update (`hookOk`) does not unlock;
- the lessor's and the auth store's sessions go through `SchemaTx`, which carries the turn.

The way back holds by `kbOpen B q := beOpen γ (q*q0) ∗ fracTok γB q` (`:46-48`): a whole `kbOpen B 1` excludes an outstanding `kbLocked`.

### F1

`backend.Snapshot.spec` (`backend__Snapshot.lean:56-65`) now:
- takes `beHistLb γ L0`;
- returns `I` with `(L0 ++ L1).getLast? = some I`, together with `beHistLb γ (L0 ++ L1)` and `beCommitted γ I`.

The new laws (`Api.lean:752-763`) are `beHist_lb`, `beHist_lb_prefix`, `beHistLb_persistent`, `_mono` and `_nil`.

The lower bound is true of the Go:
- `Snapshot`'s own `b.batchTx.Commit()` (`backend.go:381`) takes the batch lock, under which every commit (and so every append to the history, at its commit step) runs.
- So every commit in `L0` has written its meta page before `Begin(false)` reads the last one.

The bound is realizable: the backend can take a persistent `beHistLb` while it holds `beHist` inside the client's `commitOk` update, and keep it in the lock's invariant.

`beSnapN γ s I n`, the size-only form (the A11 F5 change), is consistent with `WriteTo` (`snapshot__WriteTo.lean`: some bytes of `I` of length `n` on each call) and with `Size`. The 2d user (`EtcdServer__createMergedSnapshotMessage.lean:12`) and `StateImage.lean`'s realization text are updated to the new form. The new snippet `ReqSnapshotFresh` covers the pattern; see N3 for its plumbing.

### F2

`mvccFpM m` and `keyDataOfM m` (`MvccStorage.lean:126-136`). `keyBackend_intro` gains `m : Bool`
(`:200-228`):
- with `m = true`, the pre is `beMade γ metaBkt`, as before;
- with `m = false`, the pre is nothing, and `meta`'s existence cell (`Fp.bkt metaBkt`) is in mvcc's part;
- `kbMade B .metaB` is given under `⌜m = true ∨ C.made metaBkt = true⌝`.

Plan for `NewStore` on a fresh backend:
1. `UnsafeCreateBucket(Meta)` (`kvstore.go:123`) closes by `UnsafeCreateBucket.spec`'s `some (Fm, C)` case. `Fm` contains `.bkt meta`, and `writable` holds by `Fm`.
2. The bridge's monotone `madeFlag` gives `kbMade`.
3. `mvccStorageFor` needs `D.clean` and `mvccImage_empty` of `keyDataOfM false Image.empty`. This is `KeyData.IsEmpty` (`ApiStorage.lean:161`), which does not mention `metaMade`, so it holds.

`mvccOn_held` and `LeaseBackend`'s `beTxHeld` are restated at an existential `m`. The lessor's `leaseFp` is disjoint from `mvccFpM m` for either value of `m`. The new snippet `mvcc/boot.go`'s `ReqBootNoMeta` covers `mvccrand.go:809-811`.

## Regressions (spec files changed since `1aa6fc1337`, my area)

Each was read against its callees as they are now. All close, apart from the gaps below.

- **`backend/Api.lean`**:
  - new `beTurn`, `beHistLb`, `beSnapN` (replacing `beSnap`), and `beRevert`/`beNoRevert`/`beRev`;
  - these laws are not vacuous: `beTurn_excl` is a real exclusivity, and `beHistLb_nil` is trivially true of a monotone list.
- **`MvccStorage.lean`**: see B1 and F2.
- **`Durable.lean`**:
  - `beCrash`'s three cases against `boltCrash`'s. The second case (`o = none ∧ Image.empty ∈ L`) follows from `boltCrash`'s `named = false ∧ D = Data.empty` with `σ.recovers D`, because `imgOf Data.empty = Image.empty` (`clean` is `true` in both).
  - The third case is C42: as stated, it cannot be proved from 4c/OsFs today. This is recorded.
  - `beFile_bytes` and `beFile_none` are plausible from `fileHolds_image` and `boltFresh_alloc` (both exist).
  - `boltOpenOptions_init` is an assumed `PkgInit` fact, true of `config_linux.go:29-32`.
- **`SchemaTx.lean`**:
  - the turn is threaded through the lock contracts;
  - `confStateSave_hook` closes against `confstate.go:29-36`: one `UnsafePut(Meta, confState, json(cs))`; the entry bound `128 + 21·encSize` covers JSON's at-most-20-digit numbers per proto varint; `hookWrites confStateCells` holds, since the base is kept and the put is to a cell of `Fh`.
  - Margin, not stated: the post's `bs` is existential, not the JSON encoding of `c`. No current user reads the configuration back.
- **`AuthBackend.lean`** (new): introduction and elimination laws only, over `authFp` and the opaque `authImg`. `authShare = 1/4` and `leaseShare = 1/2` leave room for the server's share. Plausible.
- **`backend__begin.lean`, `backend__unsafeBegin.lean`**: both modes, with `rtNew` holding a fresh `threadTok`. These match `backend.go:1086-1098` and close with bbolt's `statSlot_wtx` (`bbolt/Api.lean:542`). The header's text is stale (N2).
- **`backend__Snapshot.lean`, `snapshot__{Size,WriteTo,Close}.lean`**: see F1. `backend__Defrag.lean`: header only; the laws it names all exist (`dbBroken_state`, `boltFresh_alloc`, `openFileOk`, `fileHolds_alloc`, `boltRelease`).
- **`readTx__UnsafeRange.lean`, `baseReadTx__UnsafeRange.lean`**: see S1.
- **`mvcc/Api.lean`**:
  - `rangeCtxErr` replaces `context.isCtxErr`, which was false: `kvstore_txn.go:121` wraps the error with `fmt.Errorf("…%w", ctx.Err())`.
  - `rangeCtxErr_fresh` is true both in Go (a `*fmt.wrapError`) and in Perennial's `Errorf` model (an `*errorString` of the format, by `↦□` agreement).
  - The step past `Errorf`'s `ArgsWf` is a trust-boundary step, recorded in `notes/perennial-changes.md`.
  - `init.spec` adds `ErrRevisionNotFound`, which matches `key_index.go:25`, with `Nodup`.
- **`mvcc/ApiWatch.lean`**:
  - `wsOpen_closed`: see W1.
  - `wStep`'s new unconditional clause (each event is a history event at its `ModRevision` that `W` keeps) is true of the Go:
    - `kvsToEvents` filters by the group, then `newWatcherBatch` assigns events by `w.contains` and `minRev`;
    - `w.send` applies the filters;
    - a delete's `ModRevision` is patched.
  - `watch_init` adds the `Nodup` of the three errors (`watcher.go:30-32`).
- **`mvcc/watchStream__Watch.lean`, `storeTxnCommon__rangeKeys.lean`**: text only, consistent with the above.
- **`schema/Api.lean`**: `schema_norm` is a law over the opaque models, plausible for proto3 scalar, string and bytes fields.
- **`pbutil/MustUnmarshalMessage.lean`**: the post is now `mergeDst ∗ ⌜encodes ∧ norm c = c⌝`, exactly the success disjunct of `Proto.Unmarshal.spec` (`proto/Unmarshal.lean:54`). Callers that need `msgAt` get it from `mergeDst_msgAt`.

## Snippets changed or added

| snippet | verdict |
|---|---|
| `backend/parts.go` `ReqDeleteVisible` | closes (B3) |
| `backend/ranges.go` `ReqSeqRange` | closes with the added `b < end` |
| `backend/snapshot.go` `ReqSnapshotStream` | closes (`beHistLb_nil`, `beSnapN`'s `n`). `writeOk` of a `bytes.Buffer` stays an open item in open-questions. |
| `backend/snapshot.go` `ReqSnapshotFresh` (new) | the freshness part closes: `ForceCommit`'s `beReq`, `beHist_lb`, `Snapshot`'s bound, and the client's invariant "every later image keeps `k = v`". The reopen part rests on an assumption that is false of Go: N3. |
| `mvcc/boot.go` `ReqBootNoMeta` (new) | closes (F2) |
| `mvcc/compact.go` `ReqCompactDeleteReturned` (new) | closes on the `keyBackend` rows: `rangeOk`'s `rangeLent`, and the `UnsafeDelete` row returning `ks ↦*{dk} k`. The bytes really are unchanged in Go, because bbolt's `node.del` shifts inodes and never writes the mmap'd key bytes. I spot-checked this; the backend's own realization over `txBytes_acc` was not re-derived. |
| `mvccwatch/history.go`, `lifecycle.go`, `progress.go` | close now (W1, S2) |

The user patterns the completeness report listed as uncovered ("the snapshot is at least the last
commit", "mvcc over a backend without `meta`") now have snippets.

## New findings (all second-tier)

**N1. `MvccStorage.lean`'s realization text still uses `mvccFp`/`keyDataOf` where `m = false` needs `mvccFpM m`/`keyDataOfM m`.**
- Where: `:44-45` (`KeyData.mid D0 D = keyDataOf S.mid`), `:49` (`kbRead B rt D := ∃ V, beRd γ (loc rt) mvccFp V ∗ ⌜D = keyDataOf V⌝`), and `:71-78` (the rows).
- Why it matters: with `m = false`, `kbData`'s `D` has `metaMade = V.made meta`, but the stated `kbRead` would give `metaMade = true`. The shared read row (whose `kbRead` must carry `kbData`'s `D`) then does not close as written.
- Fix: restate those lines at `Fm`/`keyDataOfM m` (`kbRead … beRd γ (loc rt) Fm V ∗ ⌜D = keyDataOfM m V⌝`). The law's statement is unaffected.

**N2. `backend__begin.lean:20-21`'s text is stale.** It says `statSlot_wtx` was "requested of the bbolt group … (until it lands this step has no source)", but `statSlot_wtx.spec` exists (`bbolt/Api.lean:542`). Fix: cite it.

**N3. `ReqSnapshotFresh`'s reopen step rests on an assumption that is false of Go.**
- The assumption: `os.WriteFile` leaves a durable file.
- What Go does: it writes without `fsync` of the file or the directory.
- What the spec needs: `beFile_bytes` requires `m.named = true`, every byte synced, and `lo = hi = size`.
- Also: `backend.NewDefaultBackend` is translated with a body but has no spec file, so the snippet's proof would go through its body: `DefaultBackendConfig.spec`, then `New.spec`.
- Status: recorded in open-questions ("`os.WriteFile` is assumed").
- Fix: write the file with `Sync` and a directory sync, or state the assumption as "the file's bytes are durable, named". Add a one-line `NewDefaultBackend.spec`.

**N4 (margin, `SchemaTx.lean`'s `confStateSave_hook`).** The saved bytes `bs` are existential: the post does not say they are the JSON encoding of `c`. This is harmless today, since no verified user reads `confState` back. It should be named in the margin.

No bug in the Go code found. Nothing to add to `issues/`.

## Counts

- Original first-tier findings: 6 (B1, B2, B3, W1, F1, F2). All 6 are resolved. B2's new revert case rests on the recorded open decision C42.
- Original second-tier findings re-checked: 9. Six are resolved (provability S1-S4, completeness S3-S4); provability S5 stays open (recorded). Completeness S1-S2 were not re-checked (outside this area's files).
- Open decisions carried: A8 (O1), A9, the watch id (O3), 3.15 (O2), C42, and `os.WriteFile`.
- Spec files changed since `1aa6fc1337` in my area, re-read: 37 (backend 30, mvcc 4, schema 1, pbutil 1, plus `SchemaTx`/`AuthBackend` counted under backend). The changed files under `storage/` outside `{mvcc,backend,schema}` (`storage/Api.lean`, `OpenBackend`, `OpenSnapshotBackend`, `BackendHooks__OnPreCommitUnsafe`, `storage__*`, `wal/Api.lean`) belong to 2d/2e and were not reviewed, except where 4a's laws are cited from them.
- Snippets changed or added: 10 functions in 7 files. 9 close; 1 (`ReqSnapshotFresh`) closes in its freshness part only (N3).
- New first-tier findings: 0. New second-tier findings: 4 (N1-N4).
