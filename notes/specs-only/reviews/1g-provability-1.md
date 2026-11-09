# Batch 1g (cache, B-tree): provability review, round 1

Reviewer: provability. Read: `Spec/go_etcd_io/etcd/cache/v3/` (Api, Internal, the public specs and
the internal ones the sketches lean on), `Spec/k8s_io/utils/third_party/forked/golang/btree/`
(Api, Internal, the specs the cache and the snippets use), the snippets
`examples/specreq/{cache,btree}/`, the Go code (`.lake/src/cache/*.go`; the B-tree at
`k8s.io/utils@v0.0.0-20260108192941-914a6e750570`, the version `cache/go.mod:13` pins), 1b's
`ApiWatch.lean`, W0's `Model.lean`/`State.lean`/`Wire.lean`, Perennial's `sync` specs, the old
specs and proofs in `specs-ref`. `batch-1g.md` was read only after the findings below were written.

## First tier

### F1. No thread token: `Watch`'s `wg.Add(1)` and the read locks of `Get`, `WaitForRevision`, `WaitForNextResync` have no counted resource behind them

**Principle:** an exclusive resource the code needs is covered by a token every caller can supply
(Preferences: resources; `notes/bounds-plan.md`); sketches plausible (every resource has a source).

**Evidence.**
- `Cache.Watch` (`cache.go:142`) runs `c.waitGroup.Add(1)` once per call, and the goroutine it forks
  lives until `ctx` or the cache's context is done. Perennial's `WaitGroup.Add.spec`
  (`Perennial/Spec/sync/WaitGroup__Add.lean:31-32`) needs `oldc + delta < 2^31` from the wait group's
  owner. Nothing in `Watch.spec`'s pre bounds the number of pending `Add`s: the old proof deposited
  the caller's `threadTok` at that `Add` (`specs-ref` `Proof/.../cache/v3/InvCache.lean:444-450`, the
  counter is `k + d` with `threadToks k`; `wp_cacheWg_Add`, `:500-511`), and the old spec took and
  returned a `threadTok` (`specs-ref` `Spec/.../Cache__Watch.lean:44,47`). The new spec dropped it
  (`Cache__Watch.lean`, pre: `isCache ∗ cacheOpen c q ∗ ctxOk ∗ optsAt ∗ ⌜¬watchPanics⌝`). The token a
  goroutine gets from `wp_fork_tok` comes after the `Add`, too late to bound it.
- `Cache.Get` reads the store under `RLock`: `store.LatestRev` (`store.go:172-176`), `getSnapshot`
  (`:75`), and `waitTillRevision` (`cache.go:288`, then `revCond.Wait` on the `RLocker`, which takes
  `RLock` again). `WaitForRevision` polls `LatestRev` (`cache.go:245`). `WaitForNextResync` runs
  `notifier.wait`, which does `n.mu.RLock()` (`demux.go:384`). Perennial's `RLock` takes an
  `ownRLockToken` (`Perennial/Spec/sync/RWMutex__RLock.lean:30`), and there are only
  `actualMaxReaders` of them. A persistent `isCache` can lend them only through a thread pool
  (`Perennial/Proof/sync/RWMutexThreads.lean`), and the pool lends one only to a caller holding a
  `threadTok`. `Cache__Get.lean:33-35` justifies dropping the old `cacheReader` with "the store is
  read under its lock and its snapshots are frozen, so any number of `Get`s run at once". That
  argument covers the snapshot, not the store's `RWMutex`.
- This branch's other batches take the token in the same situation:
  `client/v3/leasing/Api.lean:67` ("takes a thread token for the cache's reader slots (given back)"),
  `leasing/NewKV.lean:16` (`wg.Add`), `client/v3/Api.lean:700` (`GetStream`).

**Callers affected:** every user of `Watch`/`Get`/`WaitForRevision`/`WaitForNextResync`. The
snippets do not show this, because no snippet threads tokens. Without the token, none of these
specs can be proved.

**Fix:** add `threadTok` to the pre and post of `Cache.Watch`, `Cache.Get`, `Cache.WaitForRevision`
and `Cache.WaitForNextResync`, given back in every post, as `leasing` does. Do the same for the
internal specs that read-lock (`store.LatestRev`, `store.getSnapshot`, `store.Get`,
`Cache.waitTillRevision`, `notifier.wait`, `demux.WaitForNextResync`, `demux.LatestRev`), or give
them a reader token borrowed from the store's or demux's pool. In `Watch`'s sketch, the token is
deposited at `Add` and a fresh one is received at the `go` statement. Fix `Cache__Get.lean`'s
Changes paragraph to match. `New`, `Close`, `Ready`, `WaitReady` and `RequestProgress` need none:
`New`'s `Add`s are a constant count, and the others use a `Mutex` or the write lock's guard.

### F2. `respFact`'s third disjunct lets through a progress notification with no quiet fact, so `enqueueResponse`, `Broadcast` and `store.Apply` cannot be proved

**Principle:** specs sound; the realizations must satisfy every spec at once.

**Evidence.** `Internal.lean:242-247`:
`respFact γ rng pos m pos' := deliv… ∨ (progress ∧ quiet …) ∨ ⌜m.events = [] ∧ pos' = pos⌝`. The
third disjunct holds for any `m` with no events, including a progress-shaped one: `hdrRev = P ≠ 0`,
not canceled, not created, `compactRev = 0`.
- `watcher.enqueueResponse.spec` takes `respFact` and leaves the producer at `pos' = pos`. The
  code sends such an `m` on `respCh` (`watcher.go`, `enqueueResponse`). The consumer then receives a
  progress notification for which `cacheWatchAt_recv` (`Api.lean:361`) owes `quiet σ.kv rng pos P`,
  and nothing supplies it.
- `demux.Broadcast.spec` takes the same `respFact`. `broadcastLocked` (`demux.go:232-240`)
  broadcasts any `IsProgressNotify()` response as progress to every active watcher
  (`broadcastProgressLocked`, `:242-256`), and `updateStoreLocked` sets `maxRev = P` (`:201-203`).
- `store.Apply.spec` takes the same `respFact`. `applyProgressNotifyLocked` sets `latest.rev = P`
  (`store.go:141-147`), which breaks `isStore`'s "gap quiet up to `lr`".

The callers do not need the gap: 1b's `watchStep` gives quiet for every progress
(`ApiWatch.lean:230-252`). Created responses and `hdr.revision = 0` responses are not progress
notifications.

**Fix:** restrict the third disjunct to responses that are not progress notifications:
`⌜m.events = [] ∧ (m.hdrRev = 0 ∨ m.created = true ∨ m.canceled = true ∨ m.compactRev ≠ 0) ∧ pos' = pos⌝`.
For `enqueueResponse`, drop the disjunct entirely: the demux never enqueues such a response to a
user watcher.

### F3. Snippet `ReqNewOptions` (`lifecycle.go`) cannot be proved: `New`'s success arm does not say `c ≠ nil`

**Evidence.** The snippet panics on `err != nil || c == nil`. `New.spec`'s success arm
(`New.lean:72-73`) gives `⌜CfgValid … ∧ err = nil⌝ ∗ isCache c γ who pfx ∗ cacheOpen c 1`.
`isCache` is opaque, and no law says `c ≠ null`. The same holds for `newCache.spec`. The code
returns `&Cache{…}` (`cache.go:81`), so the fact is true.

**Fix:** add `⌜c ≠ null⌝` to the success arm of `New.spec` and `newCache.spec`, or add a law
`isCache c γ who pfx ⊢ ⌜c ≠ null⌝`.

### F4. Root cache (`pfx = ""`): `getOk`, `cacheWatchAt_recv` and `store.Restore` can be proved only if the history has no empty key, and no W0 law gives that

**Evidence.**
- `prefixRange "" = {key := "", rangeEnd := prefixEnd ""} = {"", [0]}` (`Internal.lean:122`, W0's
  `prefixEnd`, `client/v3/Api.lean:193`), and that range contains the empty key.
- The cache's own list `c.kv.Get(ctx, "", WithPrefix())` and its upstream watch both read
  `{[0],[0]}`: `OpGet`/`OpWatch` rewrite an empty key to `"\x00"` (1b's `OpM.watchReq`,
  `ApiWatch.lean:128`).
- A client `Get(ctx, "")` (single key `""`) or `Get(ctx, "", WithPrefix())` passes `rangeOk ""`.
  Its `getOk` claims `Store.rangeKVs (σ.kv.storeAt tgt) {"", …}`, which includes key `""` if the
  history has one. The cache's snapshot never contains `""`.
- The internal pre `store.Restore.spec`, `Store.rangeKVs σ.kv.store (prefixRange pfx) kvs`, cannot
  be established from the client's `Get` answer over `{[0],[0]}`.
- The same gap arises for `deliv`'s `evsBetween h rng …` against 1b's `watchEvents` at `"\x00"`.

The model refuses empty keys at every write (`Model.lean:639`, `:821`, `:846`, `:858`, `.emptyKey`),
so the fact is true of reachable histories. But clients get no `Reach` from an initial state
(`etcdLb_reach`/`etcdLb_ord` relate reached states only), and no law states it. The root cache is
the main configuration of etcd's tests (`New(client, "")`).

**Fix:** a W0 law in `req/go_etcd_io_etcd_api_v3.md`, for example
`etcdLb γ σ ⊢ ⌜∀ r, ∀ e ∈ σ.kv.eventsAt r, evKey e ≠ []⌝` (the cluster's invariant keeps it from
`State.init` and every `Step`). Cite it in `Get`'s and `Watch`'s sketches and in `Restore`'s caller.
The alternative is to define `prefixRange ""` and `cacheRange` with `"\x00"`, but `Get(ctx, "")`
would still need `storeAt … "" = none`.

## Second tier

### S1. `demux.Broadcast`'s `respFact` is taken at the demux's position, but the watch loop re-watches from its original `rev`
`Cache.watch` (`cache.go:353-372`) calls `watchEvents(rev, …)` again with the **same** `rev` after
the upstream channel closes without an error (`watchEvents` returns `nil` at `:405-406`). By then
`demuxFeed`'s position is past `rev`. The new upstream watch's `watchStep` facts start at
`WatchPos.init rev`. When a response re-delivers an event below the demux's position, `deliv` at
that position is false, so `watchEvents` cannot meet `Broadcast.spec`'s pre. The code calls
`Broadcast` anyway, and `validateRevisions` rejects the response (`demux.go:152`). The sketch needs
one of two changes:
- state `respFact` at the upstream's position, and let `Broadcast`'s proof convert it, after
  `validateRevisions` succeeds, into a fact at its own position: every event `> maxRev`, so
  `evsBetween rev maxRev = []`;
- or add an arm for stale responses that ends in an error.

`cacheLoopRun c rev` would then carry the upstream position apart from `demuxFeed`'s. The same
applies to the re-registered `storeW` at `rev` (`:355`), which `store.Apply` rejects as stale.

Go note, not filed: after a clean close the loop re-watches from the original revision instead of
`maxRev + 1`. The demux and the store then reject the replay, reset readiness and re-list. Only
liveness and efficiency suffer; no wrong answer. A `nonissues/` candidate for the coordinator.

### S2. `store.Get`/`getSnapshot` have no lower-bound premise, so `Cache.Get` cannot conclude `L ≥ serverRev` or `L ≥ r0`
`getOk` needs `r0 ≤ L` and `σ0.kv.rev ≤ L`. The sketch gets `cacheRevLb c serverRev` from
`waitTillRevision` and `cacheRevLb c r0` from the pre. `store.Get.spec` returns
`storeRevLb s lrev` but nothing relating `lrev` to an earlier lower bound, and "`storeRevLb`
monotone" only weakens. Fix: `store.Get.spec` and `getSnapshot.spec` take `storeRevLb s r` and
return `⌜r ≤ lrev⌝`. Add an internal law between `cacheRevLb c r` and the store's `storeRevLb`, or
let them take `cacheRevLb`.

### S3. The internal sketches use opaque predicates that have no laws
`Cache.Watch`'s goroutine receives from `w.respCh` in a `select` with `watcherConsumer`, and after
close it reads `w.cancelResp`. `applyStorage` receives with `storeApplier`. `Internal.lean` has
no `watcherConsumer_recv`/`_recvAu`, no fact from `watcherStopped` about `cancelResp` (`nil`, or a
read-only response with `Canceled` and no events), no `storeApplier` receive law, and no link
between `cacheRevLb` and `storeRevLb`. Its only laws are `storeCeil_raise`/`storeCeil_lb`
(`Internal.lean:295-302`). Fix: state them as 1b does (`watchChAt_recv`/`watchChAt_recvAu`). Also
consider a `cacheWatchAt_recvAu` for clients that receive in a `select` with their context. The
snippets and `cachekv.go:82,188` use `range` only, so this is not required today.

### S4. `snapAt`/`kvTree`'s entries: `*kvItem` or `*mvccpb.KeyValue`?
`Internal.lean:22,160` says the entries are `(key, *kvItem)`. `snapCert`/`snapFor` (`:171`,
`:206`) put `keyValueOwn e.2` on them, and `snapshot.Range.spec` returns `map Prod.snd` as the
`[]*mvccpb.KeyValue` (`item.kv`, `snapshot.go:39-52`). Read as `*kvItem`, `Range`'s post is false.
Fix the text: the entries are `(key, kv pointer)`, related to the tree's `*kvItem`s through
`kvItemAt p k kv`.

### S5. The cancel arm of `cacheWatchAt_recv` says nothing
`⌜m.canceled ∧ m.events = []⌝`, then closed, with no fact. This is sound: it covers the
history-window compaction (`demux.go:330-333`, `watcher.Compact`) and the spurious one of
`issues/cache-stale-progress-compacts-newest-watch.md`. It is a margin: the code also gives
`hdrRev = 0`, `compactRev =` the demux's `nextRev` for the watcher, and
`CancelReason = ErrCompacted.Error()`. The docstring's "the cache's history no longer holds the
watch's position" is not in the formula. Either say "any time" in the docstring, or add
`m.compactRev ≤ pos` if a user needs it.

### S6. Smaller points
- `etcdPeek` is defined twice with the same body (`Cache.etcdPeek`, `Api.lean`, and 1f's). The
  request to move it into W0 is filed. Keep the cache's as a citation once it lands.
- `Cache.Get` asks for `ctxPrin ctx who` and `etcdLb γ σ0` even when serializable. That is fine:
  any caller can make an anchor from `cacheRevLb_zero` and `cacheRevLb_reached`, and the context
  premise is W0's usual one. This is a check, not a change.
- `Cache.eventOwn` has no points-to for `PrevKv`. That is harmless, since the cache refuses
  `WithPrevKV`, but a consumer cannot read the field.

## What is good

- **(a) Get.** `getOk` matches the code path for path:
  - `getSnapshot` (`store.go:74-102`) answers with the newest snapshot `≤` the target. Every
    event batch appends a snapshot (`applyEventsLocked`, `:149-170`), and progress moves `latest.rev`
    only over quiet gaps. So the snapshot is `storeAt tgt` under the prefix (`snapFor`), and
    `rangeOk` puts the range inside the prefix (`validateRange`, `cache.go:478-513`, matches
    `rangeOk` case for case, including the all-`0xff` prefix).
  - The frozen clone can be read outside the lock.
  - `L = latest.rev`.
  - The linearizable anchor is sound: inside the derived update, `etcdPeek` plus `etcdLb_reach`
    give `Reach σ0 σ1`, then `L ≥ serverRev ≥ σ0.kv.rev`.
  - The errors fit the code: `ErrFutureRev`, `ErrCompacted`, `ErrNotReady`, timeout, context,
    and `getErr`'s `ErrKeyRangeInvalid ∨ ctxDone`, including the case where `WaitReady` returns
    `ctx.Err()` even when ready (`ready.go`, `waitForState`).
  - Restores never lower the revision: the ceiling design handles the old applier draining
    concurrently with the next `Restore` (`cache.go:355-367`).
- **(b) Watch law.** `cacheWatchAt_recv` is true of the code, given the demux's invariants:
  - Events responses carry whole revisions, contiguous from the watcher's `nextRev`. This holds on
    the broadcast path (`demux.go:258-290`, `sendStart`) and on the resync path (history complete on
    `[minRev, maxRev]`; the odd `end+1 == len(events)` guard in `updateStoreLocked` is harmless,
    since the final append's `minRev` dominates).
  - Filtered-empty responses move only the demux's position.
  - Progress from `BroadcastProgress`/`BroadcastProgressTo` is quiet, because an active watcher's
    `nextRev ≤ maxRev` only over a gap with no events.
  - Every response has a header (`enqueueResponse`), `Created` is never sent, the rejected request
    has one buffered cancel, and the channel is closed by the goroutine.
  - The stale-progress bug is admitted as a spurious cancel. `quiet`/`afterProgress` tolerate a
    progress below the position, and 1b's `c ≤ P` (`ApiWatch.lean:248`) excludes the trigger
    anyway.
- **(c) `cacheOpen`.** Watch-after-Close is sound. Go allows reusing a wait group after `Wait` has
  returned, and Perennial's `Wait` gives back the wait token (`WaitGroup__Wait.lean`), so the
  realization can re-open. The new goroutine sees the cache's context done and closes its channel.
  `Close` holding the whole token excludes the `Add`-at-zero race of
  `nonissues/etcd-cache-watch-during-close-waitgroup.md`.
- **(d) B-tree.** The `ownBTree` laws are true of the code:
  - `Clone` gives two fresh copy-on-write contexts (`btree.go:597-608`).
  - `freeNode` frees only nodes the context owns (`:633-645`), so nodes shared with a clone are
    never written or recycled, and `ownBTree_persist` of a clone is sound.
  - Reads at any fraction do not mutate.
  - `Len`'s `W64 s.length` wraps as Go's `int` does.
  - The degree bounds `[2, 2^62]` are exact: `NewWithFreeList` panics at `≤ 1` (`:132`), and
    `maxItems = 2d-1` overflows above `2^62` (`:611-613`).
  - The sorted-map model (`mInsert`, `removeOp`, `ascRange`) matches the specs.
  - The `ItemOrder` departure (a persistent item predicate fixed at `New`) is the approved kind.
- **(e) Premises.**
  - `CfgValid` is exactly `newCache`'s check.
  - `CfgBounded` is needed by the code (`make(chan, n)` at `n < 0`, the ring arithmetic, `maxItems`)
    or is the model's channel limit, and it sits at the one producer. Timers with non-positive
    durations do not panic, so no premise on the intervals is needed.
  - `etcdPeek γ` is needed by the cache's own client `Get`s, and any owner of `etcdState` can
    supply it.
- **(f) Snippets.** All are provable from the stated specs and laws except `ReqNewOptions` (F3).
  The F1 tokens apply to all of them.
  - `ReqGetAfterPut`: freshness through `σ0`, and the single writer of `k`.
  - `ReqGetAgreesWithWatch`: both answers are prefixes of one history (`etcdLb_ord`), and
    `kvMatches` gives the values and mod revisions.
  - `ReqWaitThenSerializable`: `r0`.
  - `ReqRangeInvalid`: `getErr`, and `¬getUnsupported` in `getOk`.
  - `ReqWatchFromRev`: `deliv` contiguity from `some 2`, and one event per revision on `k`.
  - `ReqProgressQuiet`: `b` equals the last event's revision under the workload, and `quiet` forces
    `p ≤ last`.
  - `ReqWatchEnds` and `ReqWatchRejected`: the `closed` and `rejected` arms.
  - `ReqNewDefault`: Watch, Close, Watch, Close.
  - `ReqReadyThenGet`: `cacheRevLb c 1`.
  - The three B-tree snippets: `ownBTree_persist` for the shared clone, and `orderedOrder` for ints.

## Targets ranked by need of revision

1. **The cache's public specs**: `Cache.Watch`, `Cache.Get`, `Cache.WaitForRevision`,
   `Cache.WaitForNextResync` (F1), and `New`/`newCache` (F3).
2. **The internal demux, store and watcher specs** in `Internal.lean`: `respFact` (F2),
   `Broadcast`/`watchEvents`/`cacheLoopRun` positions (S1), `store.Get`/`getSnapshot` lower bound
   (S2), the missing internal laws (S3), the entry type (S4).
3. **`Api.lean`**: the empty-key dependency, which needs a W0 request (F4); the cancel arm's text
   (S5); the duplicate `etcdPeek` (S6).
4. **The B-tree** (`Api.lean`, `Internal.lean`, 50 specs): no finding.

## Verdict

The cache's client-facing statements, `getOk`, `cacheWatchAt_recv` and `cacheOpen`, are true of
the code and strong enough for every snippet but one. The B-tree is sound. Four findings block
provability:
- the thread tokens the wait group and the read locks need;
- the over-broad `respFact` disjunct;
- `New`'s missing non-nil result;
- the empty-key fact the root cache needs from W0.

Each fix is local, so a second round is needed only to check the repairs.
