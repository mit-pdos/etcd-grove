# Batch 1g (etcd's cache and its B-tree): completeness review, round 1

Reviewer: completeness (users, patterns, snippets). Read-only; my own findings were formed before
reading `notes/specs-only/batch-1g.md`, and its claims are checked against them at the end.

Sources: the cache at `a4d2bb17` (`.lake/src/cache` →
`/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/cache/v3@v3.0.0-20261107170612-a4d2bb1720b9`);
etcd's integration tests `tests/v3@*/integration/cache_test.go` (the four versions in the module cache
are byte-identical; line numbers below are of `v3.0.0-20261103162249-673da07c8fab`); this repository's
`examples/etcd/cache/cachekv.go`; mvcc's `index.go` (`.lake/src/server/storage/mvcc/index.go`).

## Users found

**The cache** (`go.etcd.io/etcd/cache/v3`): importers in the whole module cache are only etcd's
`tests/integration/cache_test.go` and `examples/etcd/cache/cachekv.go` (plus the snippets). No
Kubernetes module imports it (`grep -rl 'etcd/cache/v3'` over `/home/ubuntu/go/pkg/mod`). The exported
helpers `Prefix.Match`, `ExactKey`, `FromKey`, `Range`, `KeyPredForRange`, `NewDemux` have no user
outside the package; of the ten `With*` options, users call `WithHistoryWindowSize`,
`WithProgressNotifyInterval`, `WithPerWatcherBufferSize`, `WithResyncInterval`.

**The B-tree** (`k8s.io/utils/third_party/forked/golang/btree`): importers are the cache
(`store.go`, `snapshot.go`) **and etcd's mvcc key index** (`server/v3/storage/mvcc/index.go`, every
etcd server version in the module cache, including the pinned `a4d2bb17`). No `k8s.io/*` module
imports it. The mvcc user is translated with bodies on this branch
(`Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml:21-24`: `newTreeIndex`, `treeIndex.{Put,Get,
unsafeGet,KeyIndex,keyIndex,unsafeVisit,Revisions,CountRevisions,Range,Tombstone,Insert,Compact,
Keep}`), was verified against the old btree specs (`specs-ref/Proof/go_etcd_io/etcd/server/v3/
storage/mvcc/{InvIndex,treeIndex__Compact,treeIndex__Insert,...}.lean`), and is batch 3e's.

## Patterns and coverage

### Cache

| # | Pattern (what it relies on) | Call site | Snippet | Spec gives it? |
|---|---|---|---|---|
| C1 | `New` with default options never fails; with options applied in order; invalid → error | cachekv.go:126; cache_test.go:43, 443, 605, 1439-1444, 1484 | `ReqNewDefault`, `ReqNewOptions` | yes (`CfgBounded` holds of every option set the users pass, incl. `WithPerWatcherBufferSize(0)`) |
| C2 | `WaitReady(t.Context())` after `New`, `Fatal` on error | cache_test.go:48, 448, 508, ... | `ReqReadyThenGet` | yes |
| C3 | `Close` via `defer`/`t.Cleanup`, after `Watch` calls (some subtests still reading) | cache_test.go:47, 447, 1448 | `ReqNewDefault` | yes (`cacheOpen` given back by `Watch`) |
| C4 | watch from a revision: exact, gap-free, in order, no duplicates | cachekv.go:134, 76-99; cache_test.go:63-377 (`testWatch`, `cmp.Diff` of all events) | `ReqWatchFromRev` | yes (`deliv`/`evsBetween`) |
| C5 | **a revision's events come in one response** (`collectAndAssertAtomicEvents`: `Fatal` if a response starts at the previous one's revision) with txns writing several keys per revision | cache_test.go:1585-1611, used by `testWatch` and `TestCacheLaggingWatcher` | **none** (`ReqWatchFromRev` watches one key: one event per revision) | yes (`deliv` ends at `b`, next position `b+1`) |
| C6 | progress notification is quiet: `p ≤` last event (with a write per revision) | cachekv.go:162-168, 204-217 | `ReqProgressQuiet` | yes (`quiet`) |
| C7 | **progress notification is at least the last event received** | cache_test.go:567-593 (`TestCacheRequestProgress`: reads the 3 events, then `progressRev ≥ latestRev`, the last event's revision) | **none** | **no** (F2) |
| C8 | progress with `WithProgressNotify` has a non-zero revision | cache_test.go:618-630 | `ReqProgressQuiet` (partly) | yes (`hdrRev ≠ 0`) |
| C9 | watch end: closed, or a compaction's cancel then closed | cachekv.go:83, 154-157; cache_test.go:1391-1475 | `ReqWatchEnds` | yes |
| C10 | rejected request: one cancel response (unsupported option, out of prefix) | cache_test.go:380-489 (`expectCanceled`), 1478-1521 | `ReqWatchRejected` | yes; but the test also reads `resp.Err()` and its text (F5) |
| C11 | linearizable `Get` after a `Put`: sees it; header `≥` the put's | cache_test.go:740-815 (`testGet`), 1151-1332 | `ReqGetAfterPut` | yes |
| C12 | linearizable `Get` header **equals** the latest revision (no other writer) | cache_test.go:808-812, 1324-1328 | none (only `≥` is checked) | yes (`L ≤ σ.kv.rev`); snippet missing (F6) |
| C13 | `Get` at a revision agrees with the watch / with the expected KVs (`cmp.Diff`, sorted by key, full records) | cachekv.go:172-180, 244-256; cache_test.go:801-803 | `ReqGetAgreesWithWatch` | yes |
| C14 | `WaitForRevision(rev)` then serializable `Get`: header `≥ rev` | cache_test.go:757-768, 1178-1182, 805-807 | `ReqWaitThenSerializable` | yes |
| C15 | out-of-prefix `Get`: `errors.Is(err, ErrKeyRangeInvalid)` | cache_test.go:1335-1389 | `ReqRangeInvalid` | yes |
| C16 | **unsupported `Get` option: `errors.Is(err, ErrUnsupportedRequest)`** | cache_test.go:1524-1565 | `ReqRangeInvalid` checks only `err != nil` | **no** (F1) |
| C17 | `Get` above the latest revision: `errors.Is(err, rpctypes.ErrFutureRev)` (12 cases, serializable and not) | cache_test.go:784-790, 898-1117 | none | only `err ≠ nil` (F3) |
| C18 | the cache used through the `Watcher`/`Getter` interfaces, by code shared with the client (`testWatch`, `testGet`, `testWithPrefixGet`) | cache_test.go:54-63, 740-751, 1142-1151, 1577-1583 | none | different predicates from 1b's (F7; the author's open question 1) |
| C19 | a watch "from now" delivers only events after what the cache had already delivered (exactly 10 events, `TestCacheWithProgressNotify` subtest 3; "Latest-revision watcher", `testWatch`) | cache_test.go:657-701, 345-349 | none | no lower bound (F4) |

Not specifiable as safety (no finding): the counts and `wantClosed` of `TestCacheLaggingWatcher`
(timing of the resync loop), "no progress notification without `WithProgressNotify`" (a negative,
timed), `TestCacheServerRequestProgress`'s `progressRev ≥ latestRev` of writes outside the prefix
(cache_test.go:492-548: true only if no older progress is in flight; the code does not guarantee it),
the `ErrCompacted` tolerance of `testGet` (a tolerance, not a reliance).

**Keys-only.** No user relies on `WithKeysOnly` with the cache: no occurrence in `cache_test.go`,
`cachekv.go`, the cache's own tests, or any other importer (there is none). The spec states what the
code does (`getUnsupported` omits `keysOnly`, `getOk` returns full key-values: `cache.go:448-476`,
`snapshot.go:33-55`), so it is sound and serves every user. The behaviour is still a documentation
mismatch for a cache meant as a drop-in `Getter` (C18): a `nonissues/` file, blocks-proof: no; not
filed by me (read-only).

### B-tree

| # | Pattern | Call site | Snippet | Spec gives it? |
|---|---|---|---|---|
| B1 | sorted map of pointer items by an immutable key: insert/replace, delete with `ok`, point read, ascending ranges | cache `store.go:109-111, 154-162`, `snapshot.go:33-55` | `ReqSortedMap` | yes |
| B2 | a frozen clone read from other goroutines while the original is written | cache `snapshot.go:29-31`, `store.go:89-101` | `ReqFrozenClone` | yes (`ownBTree_persist`) |
| B3 | **`Get` returns the stored pointer, which the caller mutates in place (fields other than the key) while it stays in the tree** | mvcc `index.go:59-64` (`Put`: `okeyi.put`), `index.go:197-203` (`Tombstone`) | none | yes (`mLookup` returns the stored `V`; `o.item` persistent on the key only) |
| B4 | **concurrent readers of a live (not frozen) tree at fractions** (`RWMutex.RLock`: `Get`, `AscendGreaterOrEqual`), the writer re-joining the fractions | mvcc `index.go:66-70, 105-187` | none (`ReqFrozenClone` shares only a frozen clone) | yes (`ownBTree_fractional`, `_agree`) |
| B5 | **iteration stopped early by the callback** (`unsafeVisit` stops at the end key; `Revisions`/`Range` at the limit; `Equal` on a mismatch) | mvcc `index.go:97-108`, `113-134`, `250-258` | none (every snippet callback returns `true`) | yes (`iterDone`, `stopped`) |
| B6 | **`Clone` under the lock, then `Ascend` over the clone without it, while the callback re-takes the lock and `Delete`s each visited item from the original, `Panic` unless `ok`**; other goroutines write the original meanwhile | mvcc `index.go:206-229` (`Compact`) | none | yes (`Clone` gives two independent `ownBTree`s; `Delete`'s `ok = (mLookup s k).isSome`; the callback's `o.item` from `iterProtocol`) |
| B7 | a callback that reads a second tree (`b.tree.Get` inside `ti.tree.Ascend`), `Len` equality | mvcc `index.go:243-261` (`Equal`, test-only) | none | yes |
| B8 | ordered type (`NewOrdered`, `Min`, `Max`, `Len`) | none (kept: verified) | `ReqOrdered` | yes |

As far as I can check, the B-tree specs serve mvcc as the old specs did (the old `InvIndex.lean`
unfolded `ownBTree` only for what `ownBTree_items`/`_sorted` now give: `InvIndex.lean:466-560`).
Uncertain: whether batch 3e's realization can keep `o.item` persistent for every probe (`&keyIndex{key:
key}` with the request's key bytes, `index.go:54, 75, 96`): it must freeze the caller's key slice
(`↦*□`); the old proof did the same, so this is no regression.

## First tier

**F1. `Cache.Get`'s error arm does not say an unsupported request fails with
`ErrUnsupportedRequest`, which etcd's test inspects.** (Principle: "The postcondition says what the
caller inspects"; the hard rule "Complete".)
Evidence: `TestCacheUnsupportedGetOptions` (cache_test.go:1524-1565) calls `c.Get` after `WaitReady`
with each of the eight unsupported options and fails unless `errors.Is(err,
cache.ErrUnsupportedRequest)`. The code returns `fmt.Errorf("%w: ...", ErrUnsupportedRequest)`
(`cache.go:448-466`) before any context- or cluster-dependent step once the store is loaded
(`cache.go:193-202`). `getErr` (`Api.lean`) states `ErrKeyRangeInvalid` for the range check only; for
`getUnsupported o` it gives just `err ≠ nil`. `Cache__Get.lean`'s Users list attributes this test to
`ReqRangeInvalid`, which checks only `err != nil` for `WithCountOnly`; the batch report (item 4)
says "no caller inspects" the error kinds, which is not so.
Restatement: add to `getErr` the clause symmetric to the range one,
`⌜getUnsupported o⌝ -∗ (errIs err ErrUnsupportedRequest ∨ Context.ctxDone ctx)`, where `errIs` is
what `errors.Is` decides on a `fmt.Errorf("%w")` wrapping of the package's variable (a law of the
cache's API in the form of W0's `errorsIs_errVal`, `client/v3/Api.lean:1051`, or a spec of the
wrapped error's `Unwrap`). Extend `ReqRangeInvalid` with `if ctx.Err() == nil && !errors.Is(err,
cache.ErrUnsupportedRequest) { panic }`.

**F2. A progress notification's lower bound is missing: a consumer cannot conclude it is at least
the last revision it was delivered.** (Hard rule "Complete".)
Evidence: `TestCacheRequestProgress` (cache_test.go:550-594) reads the three events of its puts
(`readEvents`), calls `c.RequestProgress`, and fails unless the progress notification's revision is
`≥ latestRev`, the last event's revision. The code guarantees it: every progress sent to a watcher is
the demux's `maxRev` (`demux.go:167-198`, `350-355`) or an upstream progress above the watcher's
`nextRev` (`demux.go:242-256`), and `maxRev` is at least the last revision of every batch already
enqueued to it (`demux.go:229`, `287`); a stale upstream progress is rejected
(`validateRevisions`, `store.go:178-183`, via `demux.go:152`). The spec's `quiet h rng pos p` is
`p ≤ h.rev ∧ evsBetween h rng a p = []`, which any `p < a` satisfies, so after events up to `b`
(position `b+1`) a progress at `1` is admitted. It cannot be fixed by `a ≤ p + 1`: a watch from a
future revision (`WithRev(100)` while `maxRev = 10`) does get a `RequestProgress` notification at 10
(`demux.go:178-180`).
Restatement: track the highest revision delivered: `WatchSt.live (pos : Option Int) (seen : Nat)`
(`seen = 0` at `Watch`), the events arm moving to `.live (some (b+1)) b`, the progress arm requiring
`seen ≤ m.hdrRev` and moving to `.live (afterProgress pos p) p`. Add a snippet: read events until the
put's revision `r`, `RequestProgress`, then `if p < r { panic }`.

**F3. The B-tree's API names one user; mvcc's key index, a verified user translated on this branch
(batch 3e), relies on five patterns no snippet captures (B3-B7).** (README: "an agent scanning the
users of that API should agree that the snippets capture every aspect the callers rely on"; this is
what keeps 3e from backtracking into 1g.)
Evidence: `btree/Api.lean`'s header ("Its one user in this repository is etcd's cache") and every
`BTree__*.lean` Users line list only the cache; `examples/specreq/btree/btree.go` has no early stop,
no in-place mutation, no fractional reader, no clone iteration with deletes. mvcc's patterns are in
the table above (`index.go:54-265`). I believe the specs serve them (B3-B7, "yes"), so the repair is
cheap, but until the snippets exist nothing checks it, and B6 is the delicate one (iterating a clone
while the original is written by other goroutines and by the callback itself, with `Delete`'s `ok`
relied on through `lg.Panic`).
Restatement: list `server/v3/storage/mvcc/index.go` in the header and in the Users of `New`, `Get`,
`ReplaceOrInsert`, `Delete`, `Clone`, `Ascend`, `AscendGreaterOrEqual`, `Len`; add snippets: (a)
`ReqMutateInPlace` (insert `&ki{key, n}`, `Get` it, `it.n++`, `Get` again sees `n+1`); (b)
`ReqFractionalReaders` (two goroutines `Get`/`AscendGreaterOrEqual` under an `RWMutex` read lock, then
a write under the lock); (c) `ReqStopEarly` (`AscendGreaterOrEqual` returning `false` at an end key:
exactly the keys in `[start, end)` visited); (d) `ReqCompactClone` (clone under a lock, ascend the
clone unlocked, in the callback lock and `Delete` the item from the original, `panic` unless `ok`,
while another goroutine inserts new keys under the lock).

## Second tier

**F4. A watch "from now" has no starting bound.** `WatchSt.live none` lets the first events be from
any revision. The code starts it at the demux's `maxRev + 1` (`demux.go:98-107`) or, before any
event, at the upstream watch's start `R + 1` above the store's `R` (`cache.go:336`, `demux.go:120-144`),
so its events are all above any `cacheRevLb c r0` the caller held at the call (the store's revision
never exceeds the demux's `maxRev` but right after a `Restore`, when every event is above it).
Users rely on a version of this by timing (C19: `TestCacheWithProgressNotify`'s exact count of 10,
`testWatch`'s "Latest-revision watcher"), so no user is unserved in a way the code guarantees; but a
client that wants "only writes after X" has to use `WithRev`. Suggested: `Watch` takes `cacheRevLb c
r0` and starts at `.live none` with every delivered event above `r0` (a floor in `WatchSt`, merging
with F2's `seen`). Check the stale-progress issue (`issues/cache-stale-progress-compacts-newest-watch.md`):
there a from-now watch registers at `P+1 ≤ R` but is cancelled before any event, so the floor holds.

**F5. `watchRespAt` does not state `closeErr = nil` (nor `CancelReason`).** A consumer using the
idiomatic `if err := wresp.Err(); err != nil` (`client/watch.go:123-137`) cannot conclude `Err()` is
`nil` on an events response or what it says on a cancel; `TestCacheUnsupportedWatchOptions`
(cache_test.go:1507-1519) checks that `resp.Err()`'s text contains `ErrUnsupportedRequest`'s.
`cachekv.go:72-75` avoids `Err()` for exactly this reason. The cache never sets `closeErr`
(`cache.go:129-133`, `watcher.go:43-81`, `demux.go`): add `v.closeErr' = nil` to `watchRespAt`
(true of every cache response), and the rejected arm's `CancelReason` as the rejection's text if the
test pattern is to be served (`Cancel` with `err.Error()`, `cache.go:126-134`).

**F6. Missing snippets for patterns the specs serve**: C5 (a multi-key txn's events in one response,
`collectAndAssertAtomicEvents`), C12 (a linearizable `Get`'s header equals the cluster's revision
when the caller knows there is no other writer: the upper bound `L ≤ σ.kv.rev`), C17 (`Get` above the
cluster's revision fails: derivable as `err != nil`, since `getOk` needs `o.rev ≤ L ≤ σ.kv.rev`).

**F3'. `Get`'s `ErrFutureRev` is not classified** (C17). The test's `errors.Is(err,
rpctypes.ErrFutureRev)` cannot be fully promised (a linearizable `Get` can fail in the client's own
`Get` first, `cache.go:209-212`), but the serializable path after readiness is deterministic
(`store.go:84-89`): `o.serializable ∧ sint.Z o.rev > L` for the latest `L` gives exactly `ErrFutureRev`.
Worth stating if F1's `errIs` machinery is added; otherwise record as margin and correct the batch
report's item 4.

**F7. The drop-in pattern (C18).** etcd's tests run one `testWatch`/`testGet` against the client and
the cache through the `Watcher`/`Getter` interfaces. Under the current specs these are two proofs
(`watchChAt` vs `cacheWatchAt`; `kv.Get.spec`'s answer vs `getOk`'s). The author's open question 1
proposes unifying with 1b's watch vocabulary and a cache-specific cancel arm; I agree, and the users
confirm the need (these tests are the only drop-in users; there is no Kubernetes one). Not first tier
because each concrete call is served.

## Third tier

- `kvMatches` leaves a delete event's other `KeyValue` fields unspecified; `testWatch` compares
  delete events with `cmp.Diff` against `{Key, ModRevision}` only (cache_test.go:85-91). True of
  etcd's tombstones; belongs to W0/1b's event model, not the cache.
- `testGet` compares `resp.Kvs` with `cmp.Diff(nil, ...)` for an empty answer (cache_test.go:864-
  873): the cache returns a `nil` slice (`snapshot.go:34`); `getRespM` with `kvs = []` does not say
  `nil` vs empty. Only a test's exact-equality artefact.
- Close's margin ("every watch channel is closed after `Close`") has no user that relies on it.

## Establishable pre, sufficient post (one call site per pattern)

- `cachekv.go:126` `New(cli, prefix)`: `isClient`, `etcdPeek γ` from the caller's invariant over
  `etcdState`, `cfgOptsAt sl []` (empty slice), `CfgValid → CfgBounded` of `defaultConfigM` (pure).
  Post: `isCache` and `cacheOpen c 1`. Sufficient.
- `cachekv.go:134` `Watch(wctx, prefix, WithPrefix(), WithRev(2))`: `cacheOpen c q`, `ctxOk` of a
  `WithCancel(Background())`, `¬ watchPanics`. Post `.live (some 2)` or closed: collect's checks
  follow from `deliv`. Sufficient.
- `cachekv.go:174` `Get(gctx, prefix, WithPrefix(), WithRev(r))`: `ctxPrin` of a `WithTimeout`
  context without metadata, `etcdLb γ σ0` from the invariant, `cacheRevLb c 0` (`cacheRevLb_zero`).
  Post: `rangeKVs (storeAt r)`, combined with the watched events through the history. Sufficient.
- cache_test.go:586-592 `RequestProgress` then `waitForProgressNotify`: pre fine; post insufficient
  (F2).
- cache_test.go:1559-1560 unsupported `Get`: pre fine; post insufficient (F1).
- cache_test.go:758 `WaitForRevision(t.Context(), baseRev)` then `Get(..., WithSerializable())`:
  `cacheRevLb c baseRev`, then `r0 ≤ L`. Sufficient.
- cache_test.go:1439-1444 `New(..., WithPerWatcherBufferSize(0), ...)`: `CfgBounded` at 0 holds.
- mvcc `index.go:209` `Clone` under `ti.Lock()` (whole `ownBTree`), `index.go:212-228` the clone's
  `Ascend` with `Delete` on the original: pre establishable (the lock's invariant gives the
  original's whole share inside the callback), post `ok = isSome` against mvcc's invariant.
  Sufficient as far as I can tell (no snippet: F3).

No premise is violated by a real call: `¬ prefixAndFromKey` (no user combines them), `CfgBounded`
(every option value used is in range), `¬ watchPanics` (no lease or range option on a watch),
`ctxPrin` (tests' `t.Context()`, cachekv's background-derived contexts carry no metadata).

## Locality and abstraction (briefly)

The client-facing cache specs mention only `isCache`, `cacheOpen`, `cacheRevLb`, `cacheWatchAt` and
W0's model; `Internal.lean` stays internal. `Get`'s pre takes `etcdLb γ σ0` and `cacheRevLb c r0`
as anchors, which every caller has (`cacheRevLb_zero`). Nothing to add beyond F7.

## Ranking of the targets by need of revision

1. `Cache__Get.lean` / `getErr` (F1, F3', F6 Users list).
2. `Api.lean`'s `WatchSt`, `quiet`, `cacheWatchAt_recv`, `watchRespAt` (F2, F4, F5).
3. `btree/Api.lean` header, the `BTree__*` Users lines, `examples/specreq/btree/btree.go` (F3).
4. `examples/specreq/cache/{get,watch}.go` (F1's, F2's and F6's snippets).
5. `Cache__Watch.lean` (F4, F7). The rest (`New`, `Close`, `Ready`, `WaitReady`, `WaitForRevision`,
   `WaitForNextResync`, `RequestProgress`, the options) serve every user as written.

## Against the author's report (read after the above)

- Item 4 ("no caller inspects `ErrCompacted`/`ErrFutureRev`/`ErrCacheTimeout` beyond logging") is
  wrong for `ErrFutureRev` (12 `errors.Is` cases in `testGet`) and misses `ErrUnsupportedRequest`
  (F1).
- The keys-only finding is confirmed, with no user relying on keys-only; recommend filing it in
  `nonissues/` (blocks-proof: no).
- The header's "its one user" for the B-tree misses mvcc (F3).
- Open question 1 (drop-in watch vocabulary) is supported by the users (F7).

## Verdict

Not done: three first-tier findings. F1 (`ErrUnsupportedRequest` not stated, inspected by etcd's
test) and F2 (no lower bound on a progress notification, relied on by `TestCacheRequestProgress`,
true of the code) are gaps in the cache's client-facing post; F3 is a missing user (mvcc's key index,
batch 3e) of the B-tree whose five patterns have no snippet, though the B-tree specs appear to serve
them. All three repairs are local (a clause in `getErr` with an `errors.Is` law, a `seen` revision in
`WatchSt`, snippets and Users lines). Everything else the users rely on is covered.
