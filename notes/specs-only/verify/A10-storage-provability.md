# A10-storage, provability (verification round, 2026-11-09)

Area: batches 3e (mvcc core), 3f (mvcc watch, `pkg/v3/adt`), 4a (backend), 4b (schema, `traceutil`,
`pbutil`, `ioutil`, `httputil`, the boundaries `semver`, `x/time/rate`, `probing`, otel). Reviewed at
`1aa6fc1337` against the pinned Go (`.lake/src/{server,pkg}`). Findings written before reading the
authors' notes; afterwards checked against `open-questions.md`, `integration-*.md`, `reviews/`.

## Verdicts

| batch | verdict | first-tier |
|---|---|---|
| 3e mvcc core | PASS (spot-checked: see Coverage) | none |
| 3f mvcc watch, adt | **FAIL** | W1 |
| 4a backend (incl. `MvccStorage`, `Durable`, `LeaseBackend`, `SchemaTx`) | **FAIL** | B1, B2, B3 |
| 4b schema, pkg leaves, boundaries | PASS (spot-checked) | none |

## First-tier findings

### B1. `keyBackend_intro`'s lock rows do not close (4a, `backend/MvccStorage.lean`)

The realization keeps mvcc's batch part in `kbData` between sessions and a token while a session runs:
`kbData B D := ∃ V, beVis γ mvccFp V ∗ ⌜D = keyDataOf V⌝ ∗ (∃ C, beCur γ mvccFp C ∗ … ∨ lockTok γB)`
(`MvccStorage.lean:28-30`); `kbLocked` holds `beCur γ mvccFp C ∗ lockTok' γB` (`:31`).

The step that does not close: the `LockInsideApply`/`LockOutsideApply` rows (`ApiStorage.lean:452-464`).
After `batchTxBuffered.LockOutsideApply.spec` returns `beSess γ q Fp.none (Sess.init I)`, the row fires
`kbObs B Ψ` and must build `kbLocked B q D D`, which needs `beCur γ mvccFp C` out of `kbData`. If `kbData`
is in its `lockTok γB` case there is no contradiction to derive. In fact no other session can be open,
because the backend's mutex excludes it. But the proof cannot see that: the earlier session's `beSess`
sits in someone else's `kbLocked`, and `beSess_excl` needs both in hand. No 4a law ties a fresh session
to anything a client can park:
- `beOpen` and `beLive` have no validity law;
- `Pk` is the opener's, passed through unchanged (`keyBackend B Pk` at the same `Pk`), so the bridge
  cannot add to the lock's invariant.

mvcc's store does lock concurrently (the apply thread's `Write`, the compaction job's
`LockOutsideApply`), so the case has to be handled. The same gap reaches the way-back conjunct
(`:200-202`): from `storageRest B n` it must produce `beCur`, but `kbOpen B 1 := beOpen γ q0` cannot
exclude an outstanding `kbLocked`. That one is fixable inside the bridge, with a bridge-owned fraction
in `kbOpen`'s realization.

- **Callers affected:** the server's proofs (2d/2e: `NewServer.lean:95-102`), and through them every
  mvcc store spec, which rests on `keyBackend`.
- **Suggested fix** (a 4a law, not a bridge edit). Give a client a way to park lock-scoped state:
  - (a) `Unlock` takes, with its two updates, the `beCur γ F C` of the published footprint into the
    batch lock's invariant, and `Lock*` hands it back given a persistent `beParked γ F`; or
  - (b) a session-generation pair: `Lock*` gives `beSessNo γ n`, `Unlock` (after its updates) gives a
    persistent `beEnded γ n`, plus a law `beSess … (n) ∗ beStarted γ m ⊢ ⌜m < n → beEnded m⌝`.

  Then restate `kbData`/`kbLocked`'s realization over it.
- **Status:** not recorded (no `open-questions.md` or integration entry).

### B2. `Durable.beCrash` concludes at the crashed generation's heap (4a, `backend/Durable.lean:86-94`)

`beCrash.spec` concludes `beFile (GF := GF) p (some I)` at the current `hG`. Its source,
`Bbolt.boltCrash.spec` (`bbolt/Api.lean:523-531`), gives `@fileHolds … ⟨hG.goose_globalGS, L'⟩ γ.path D`,
which is the next generation's heap. `beFile`'s realization is `fileHolds` at its own heap, so the law
cannot be proved from `boltCrash`, and a restart cannot use its conclusion. The restart then has no
source for the `beFile` its `New` needs:
- 2d's item 3 (a restart finds a committed image);
- 2e's `memberDisk`;
- 3c's item 4.

The header's own fix (`:24-40`) is now possible: step 1 (heap binders on the opaque predicates) landed
at `1aa6fc1337`, and `#check @beFile` now takes `hG`. Step 3 is not done. The header's description of
step 1 as still missing is stale.

- **Fix:** conclude `@beFile _ _ _ GF ⟨hG.goose_globalGS, L'⟩ p (some I)`, as `boltCrash` does, and
  update the header.
- **Status:** a recorded gap (`integration-I6.md:180-189`, item 2). It still counts: the law, as
  stated, is not provable.

### B3. Snippet `backend/ReqDeleteVisible` is unprovable, and false in Go (`examples/specreq/backend/parts.go`)

The snippet asserts that a key deleted in a session is not read through a `ConcurrentReadTx` begun after
`Unlock`. Its spec, `concurrentReadTx.UnsafeRange.spec`, gives `lingerSingle`: for a key the view lacks,
the range returns nothing or a value the key had before a delete. So the snippet's `len(ks) != 0` panic
does not follow from the spec, and the spec is right.

The Go run that panics:
1. `k` was written back by an earlier session and not yet committed.
2. This session's `Unlock` writes back (`bufVersion++`, `tx_buffer.go:114`).
3. Another goroutine's `ConcurrentReadTx` copies the read buffer, which still holds `k`, into the cache
   (`backend.go:335-359`).
4. The commit resets the buffer without bumping the version (`read_tx.go:133-138`).
5. The snippet's `ConcurrentReadTx` reuses the stale copy and reads `k`.

This is `issues/etcd-backend-read-buffer-cache-stale-after-commit.md`, open decision F6 (`open-questions.md`,
4a round 1 Q7).

- **Fix:** read through the shared `ReadTx()` with `RLock` (`rdRange`'s single key is exact), or state
  the snippet as depending on F6's fork fix.

### W1. No law excludes `wsClosed` while `wsOpen` is held, so `Watch` may always fail (3f, `mvcc/ApiWatch.lean`)

`watchStream.Watch.spec`'s error disjunct is `⌜empty⌝ ∨ wsClosed ι` (`watchStream__Watch.lean:82`).
`wsClosed` is persistent, and no law relates it to the exclusive `wsOpen`: the laws are listed at
`ApiWatch.lean:336-408`, and none mentions `wsOpen`. So a caller that holds `wsOpen ι` cannot refute a
refusal of a valid range.

These snippets panic on a refused `Watch` and are unprovable:
- `mvccwatch/lifecycle.go`: `ReqFreshIds`, `ReqCancel`, `ReqClose`;
- `mvccwatch/history.go`: `ReqFromStart`, `ReqFromCurrent`, and the other `history.go` snippets that
  `Watch`;
- `mvccwatch/progress.go`: every snippet.

v3rpc's `recvLoop` also needs it to answer a valid create as created. This is a different point from
3f round 1's (d), which is about `Watch` after `Close`.

- **Fix:** add `wsOpen_closed.spec : ∀ ι, wsOpen ι ∗ wsClosed ι ⊢ False`. It is true of the
  realization: `Close` spends `wsOpen` and is the only source of `wsClosed`.

## Second-tier findings

- **S1. `readTx.UnsafeRange.spec`/`baseReadTx.UnsafeRange.spec` admit a duplicate entry.** The case: a
  non-`nil` empty end (`es ≠ nil`, `e = []`), `limit ≠ 1`, on a safe-range bucket that a pre-commit hook
  writes. The bucket check only asks `bi.safe = true`; the hook clause holds by `e = []`.
  - What Go does: the buffer finds the hook's leftover key, then bbolt's cursor finds it again. The
    limit was set to `MaxInt64`, the `len(endKey)==0` branch of `unsafeRange` resets it to 1, and the
    result has two entries (`read_tx.go:78-121`).
  - Why the spec is wrong: `rdRange` with `e = []` says `single`, at most one entry.
  - It does not happen in etcd (the hooks write only `meta`), but the spec quantifies over any `Fh`.
  - **Fix:** require `es = slice.nil` when `e = []` (as mvcc's `rangeOk` does), or keep the hook
    clause for `e = []`.
- **S2. `recvEvents`'s `resp.WatchID != id` panic is unprovable** (`mvccwatch/history.go:39`).
  `wsRespOk` admits a stream-wide `-1` progress at any time; only `RequestProgressAll` sends one, but no
  spec says so. Skip `-1` responses, as `nextNonProgress` does.
- **S3. `ReqSeqRange` does not assume `b < end`** (`backend/ranges.go`). With `end ≤ b` the unlimited
  range has one entry and the snippet panics.
- **S4. Stale names in `MvccStorage.lean`'s header.** `beHookRun_intro` (`:73`) is `LeaseBackend.lean`'s
  `leaseHookRun_intro`. `hookRun_mvcc` (`:45`, `:73`) is not a law; it is the fourth conjunct of
  `keyBackend_intro`'s post.
- **S5. Uncertain.** `ReqSnapshotStream`'s `writeOk` of a `*bytes.Buffer` depends on Perennial's
  `bytes.Buffer.Write` spec meeting `writeOk`. I did not find it stated as a law here.

## What is good

**`keyBackend_intro`, row by row (4a ↔ 3e).** Every row except the lock rows maps onto a 4a triple, and
each premise has a source:

| row | how it closes |
|---|---|
| `BatchTx`, `ReadTx` | `kbBatchTx B = btIface γ` |
| `ConcurrentReadTx` | `beHookFp` and `Fp.disj mvccFp Fh` from the intro's premise; `l ≠ rtLoc γ` gives `rt ≠ kbReadTx B` |
| shared `RLock`/`RUnlock` | `kbObs` opened and the `beVis γ mvccFp` it contains handed to `readTx.RLock`'s update |
| concurrent `RLock`/`RUnlock` | the concurrent read transaction's triples, with `beRd` |
| bare lock rows | `Fp.none` with `beVis_none` |
| shared range | `rdRange`'s safe case equals `KeyData.rtRange` with `cs = A`, `bs = B`. The unlimited case needs `|A|+|B| ≤ 2^63-1`, which the returned slices' lengths give. `covers mvccFp` holds; the `Fh` clause comes from disjointness |
| concurrent range | `lingerSingle` equals `KeyData.linger`; `metaMap` agrees on `sched`/`fin` |
| batch range | `btRange` equals `bkRange` via `beSess_cur` |
| `UnsafeCreateBucket` | `some (mvccFp, C)`, or `none` with `beMade` |
| puts | `Sess.fresh` from the row's freshness over `D0 = keyDataOf S.base` and `D`; `kbEntryMax = bboltEntryMax = 2^28` |
| delete | `beDelHeld` |
| `Unlock` | `keyDataOf S.mid = KeyData.mid D0 D` holds by the delete row's premise (b) and the fresh-put premise; the inner update gives `keyDataOf S.fin = keyDataCur S C` |
| `ForceCommit` | `beReq` |
| safe-range lock, `Size`/`SizeInUse`/`OpenReadTxN` | 4a's triples (`LockForSafeRangeDelete`, `UnlockForSafeRangeDelete`, `Size`, `SizeInUse`, `OpenReadTxN`) |
| `hookRun` conversion | holds at `H := beSess γ (q*q0) Fp.none S` |
| `kbHeld` lending to the lessor | `sameOn mvccFp`; `beNoVis` lease cells |
| reader-slot arithmetic | `mvccReaderN ≥ 2^29+4`; `+2^27 ≤ 2^30-2` is satisfiable |

**The watchable store against 1b's contract.** mvcc's `wStep`/`progStep`/`posOf`/`posEvOf` line up with
the client's `watchStep`:

| client's `watchStep` | mvcc |
|---|---|
| events from `done+1`, exact under `exactFrom` | events from `posOf+1`, exact under `exactFrom` |
| position after a progress set to `P` | `posOf` moves to the progress revision |
| compaction compared with `evDone` | compaction compared with `posEvOf` |
| `hdr.revision ≤ σ.kv.rev` | `r.rev ≤ h.rev`, with `mvccLb` and `histLe` (`exactFrom` and `wEvents` are monotone along a prefix-extending history) |
| `WEv.ofEvent` | `evOf` |

The resent-compaction gap is `issues/etcd-watch-compacted-resent.md`, handled above mvcc. `prevKV`, the
`Created` response and fragments are 2b's.

**The crash law against bbolt's, apart from B2.** `beHist` "committed or attempted" with the commit step
firing before bbolt's meta write matches `σ.recovers`. `beSynced` stands for `σ.dur = some _`. Defrag
keeps the image (rename atomic, both files the last commit's).

**Elsewhere.**
- `Unlock`'s two-update statement (`Sess.mid`, then `Sess.fin`) is exact against `batch_tx.go:328-406`,
  including the hook leftovers and the no-commit case.
- `rdRange`'s split form is right for `read_tx.go:78-121`.
- The `traceutil`, `pbutil`, `ioutil`, `httputil`, `rate`, `semver` and otel specs match their Go
  (checked: `trace.go:122-211`, `pbutil.go`, `reader.go`, `rate`'s `Delay` ≥ 0).
- The `adt` `find` descent is complete for duplicate intervals, so `Find` and `Delete` are right.

## Proof plans (spot-checked specs)

- **`batchTxBuffered.Unlock`:**
  1. If `pending ≠ 0`: `readTx.Lock`, `writeback` (first update at `Sess.mid`), `readTx.Unlock`.
  2. If there were deletes or `pending ≥ limit`: `commit(false)`. It runs the hooks (`hookOk` from `Pk`
     and a session at `Sess.mid`), hands the old read transaction to its rollback goroutine (forked
     with the thread token the read transaction held), and commits bbolt (the second update, then
     `commitOk`).
  3. With no commit there were no deletes, so `Sess.mid` equals `S.cur`, and the second update fires
     at once.
  4. `batchTx.Unlock` releases the mutex with `Pk`.
- **`readTx.UnsafeRange`:**
  1. The buffer's range, cut first. Buffer keys are above bbolt's by `Sess.fresh` for safe buckets;
     non-safe buckets read at most one entry.
  2. The bucket cache under `txMu`.
  3. `unsafeRange` on the cursor; the result is `A.take m ++ B.take n` (but see S1).
- **`watchStream.Watch`:**
  1. The empty check (`bytes.Compare`).
  2. Under `ws.mu`: `closed` gives the error; otherwise `id = nextID = n`, since no live id is
     skipped with auto ids.
  3. `watchable.watch` fires the read update under `s.mu`/`revMu`; `wsReg` is stamped with the send
     count.
  4. `SpanFromContext` from `ctxSpanOk`.
- **`keyIndex.put`/`tombstone`/`get`/`restoreTombstone`:** the `lg.Panic` paths are excluded by
  `Rev.gt`, `kiIsEmpty = false` and `gens = []`. The paths match `key_index.go:80-153`.
- **`Tracer.Start`, `EnsureTrace`, `Get`:** `ctx.Value(TraceKey{})` through `ctxTraceIs`; `IsEmpty`
  through the persistent `traceEmpty`; `WithValue`; matches `trace.go`.
- **`MustUnmarshalMessage`:** `Proto.Unmarshal.spec`'s error disjunct is refuted by the
  `encodes ∧ depth < depthMax` premise.
- **`NewLimitedBufferReader`:** `0 ≤ n` makes `np[:n]` safe; `readerAt_wrap` exists (`net/http/Api.lean:549`).

## Snippets

Checked line by line against the specs: 33 of 80.
- `backend/`: all 12.
- `mvcc/`: `store.go` (8), `compact.go` (2), `restore.go` and `boot.go` (5).
- `mvccwatch/`: `lifecycle.go` (4), `history.go`'s first 2.

Of these, 28 close and 5 do not:
- `ReqDeleteVisible` (B3);
- `ReqFreshIds`, `ReqCancel`, `ReqClose`, `ReqFromStart`/`ReqFromCurrent` (W1, one finding);
- `ReqSeqRange` needs S3's added assumption.

For the remaining 47 I read only the headers' `Assumes`/`Specs` lines:
- `mvccwatch/progress.go`, the rest of `history.go`, `mvccwatch/store.go`: they inherit W1 where they
  `Watch`.
- `schema/`, `pkgleaves/`, `adt/`, `mvcc/{lease,hash}.go`: no problem visible at that level (uncertain).

## Coverage and counts

The area has 442 spec files: 373 with function triples and about 127 law definitions.
- **Read against Go:**
  - backend: 30 triples, every law of `Api.lean`, `MvccStorage.lean`, `Durable.lean`, and
    `LeaseBackend.lean`'s list;
  - mvcc: 18 triples, every law and contract of `ApiStorage.lean` and `ApiWatch.lean`, plus
    `Api.lean`'s contracts for `Read`/`Write`/`Rev`/`Range`/`Put`/`DeleteRange`/`Compact`/`Restore`;
  - schema: 5 triples, and `SchemaTx.lean`'s header;
  - adt: 6 triples and 4 laws;
  - traceutil: 17 triples and 13 laws;
  - pbutil 2, ioutil 1 + 2 laws, httputil 1;
  - boundaries: semver 7 + 5 laws, rate 5 + 2, probing 2, otel 4.
- **Not checked:** the remaining internal mvcc specs (about 110 files: `treeIndex`, `watcherGroup`,
  hash, restore helpers) and about 65 schema triples, apart from a name-existence sweep. That sweep
  found only S4.
- **Totals:** about 130 specs and 90 laws checked; about 127 and 88 close.
  - Do not close: the two `keyBackend_intro` rows (B1), `beCrash` (B2), `readTx`/`baseReadTx.UnsafeRange`
    (S1).
  - Vacuity: no predicate found whose laws all hold at `True`.

## Ranked by need of revision

1. `backend/MvccStorage.lean` (B1), with a new 4a law in `backend/Api.lean`.
2. `mvcc/ApiWatch.lean` (W1: one law).
3. `backend/Durable.lean` (B2).
4. `examples/specreq/backend/parts.go` (B3), `ranges.go` (S3), `examples/specreq/mvccwatch/history.go` (S2).
5. `backend/readTx__UnsafeRange.lean`, `baseReadTx__UnsafeRange.lean` (S1).
6. `MvccStorage.lean`'s header names (S4).

No new bug in the Go code. The one Go misbehaviour involved, B3's, is already filed as
`issues/etcd-backend-read-buffer-cache-stale-after-commit.md`.
