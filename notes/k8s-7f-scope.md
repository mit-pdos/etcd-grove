# k8s etcd3 stage 7f, watches: Scope (2026-11-08, branch `k8s-7f`; to etcd-grove-81 for review)

The stage is the 7f bullet of `notes/k8s-etcd3-plan.md`, "Phase 7". Its target is the `etcd3` case
of Kubernetes' `TestCorrectness` at `k8s.io/kubernetes` `878cfa6c4cc7`
(`test/integration/apiserver/storage/correctness_test.go`):
- `RunWatchTraffic`: 16 watchers, with slow, hiccup and stalled consumers;
- `WatchValidator.ValidateWatch` (`k8s.io/apiserver` `9c4ec15b8038`,
  `pkg/storage/testing/correctness/watch.go`);
- the code under test is apiserver's etcd3 watcher (`pkg/storage/etcd3/watcher.go`, `event.go`).

The pins are 7d's and 7e's, with etcd fork `673da07c8f`. `lean` has since moved the etcd pin to `a4d2bb172`
(sweep repairs R1-3a, `purgeFile` only), which touches nothing here. This stage changes notes and Go only:
no Lean is edited and nothing lands until 81 approves.

**The Go prototype** (§8) is `notes/k8s-7f-proto.patch`, a patch against branch `k8s-7e`
(`736463a4bd`): the driver's watch traffic and check, and `lintest.RunLin2`.
- It passes on real runs: one member, and six partition schedules × 5 runs, all under the 32G cap,
  with peak RSS below 90 MB.
- Porcupine rejects each of five kinds of corrupted watch event.

**Three findings shape the stage:**
1. **The validator, as upstream writes it, would make the closed theorem false.** The etcd3
   watcher can deliver events after a `watch.Error` event (§2.4,
   `nonissues/k8s-etcd3-watcher-events-after-error.md`, reproduced 8/50).
2. **Replaying the validator along porcupine's linearization is unsound once failed writes are
   allowed.** This is 7d §2's trap. So watches become porcupine operations, checked against each
   configuration's history (7e's `hist`) (§4).
3. **The store's watches use two etcd paths that no proof covers yet: `WithPrevKV` and
   `WithRequireLeader`** (§2.3). The second makes the deployment premise
   `v3rpc.runsNoRequireLeader` false for this driver, and that premise is in every etcd closed
   theorem. G1 itself needs no more Goose work: its fix landed (Perennial `898c0ddc5`, §3).

## 1. What the watch traffic and the validator check

**The traffic** (`traffic.go:264-311`, `578-626`, `688-776`):
- 16 goroutines loop until the unary traffic ends (`stopWatches`). Each one draws a request,
  runs one watch, keeps the last non-error event's object as its cached object, and sleeps out
  the rest of `HiccupDuration` (150 ms).

**A request** (`randomWatchRequest`):
- **SendInitialEvents**: true 30% (a "watch-list" request). Then AllowWatchBookmarks is true,
  Match is NotOlderThan, and no future RV is drawn.
- **RV**: empty, `0`, `1`, cached, current, past, future, 15% each but `1` (10%). The relative
  ones are relative to `GetCurrentResourceVersion`.
- **RV `""` or `"0"` without watch-list**: SendInitialEvents is false, with NotOlderThan.
  Otherwise it is nil, with match `""`.
- **Key**: existing 80%, a missing namespace 10%, a missing object 10%.
- **Scope**: cluster 40%, namespace 30%, object 30%. Then `Recursive` is drawn again (70%).
- **Selectors**: 7e's field and label selectors.
- **AllowWatchBookmarks**: 50%.

**Consuming a watch** (`runWatch`):
- The context is `WithTimeout(2s + 150ms)`. The watch is read for `Duration` (500 ms) or until
  `MaxEvents` (200).
- Slow: 2 ms between reads. Hiccup: one 150 ms pause after the first event.
- Stalled: reads nothing for 150 ms, then returns no events.
- After a `watch.Error` event it reads once more, and reports an error if the channel is still
  open.
- A `Watch` error that is not a `StorageError` or a 429 **panics**.

**The validator** (`watch.go:47-92`, against `Replay`, the model replayed along porcupine's
linearization):
- `checkWatch`: the expected error for an invalid request (none in the traffic).
- `response.Err` must be nil (or 429).
- `validateMaybeLastEventError`: at most one Error event, a `metav1.Status` with `Failure`, and
  **last**.
- `validateBookmarks`: bookmark RVs never decrease and are at least the last event's. Every event
  after a bookmark is above it. At most one initial-events-end bookmark.
- **For a watch-list request**:
  - the events before the first bookmark are the initial events;
  - that bookmark must carry the initial-events-end annotation;
  - its RV is at least the requested one;
  - the initial events equal `Model.initialEvents` (an Added per matching item, in key order) at
    the replay's state at the bookmark's RV;
  - no bookmark but some events is an error.
- `validateReliable`:
  - the range `[Min, Max)` comes from the events' RVs (an event `r` covers `[r, r+1)`, a bookmark
    `b` covers `[b+1, b)`), then is clipped by the request: `Min = RV+1` for Exact or a non-zero
    legacy match, and `max(Min, RV+1)` for NotOlderThan;
  - the non-bookmark events must equal exactly the replay's changes in that range that are in
    scope;
  - each change is turned into an event by the predicate on the new and the old object:
    Modified, Added, or Deleted (the old object at the change's RV);
  - events compare by key, type, RV and object.

So the validator checks that each watch is a gap-free, duplicate-free, correctly filtered
window of the history. The window starts at the requested revision. For a watch-list it starts
with a correct snapshot.

## 2. The etcd3 watcher

### 2.1 Structure

**`store.Watch`** (`store.go:1142`):
- `prepareKey`, then the versioner's `ParseResourceVersion`;
- then `watcher.Watch(clientv3.WithRequireLeader(ctx), key, rev, opts)` (`watchContext`).

**`watcher.Watch`** (`watcher.go:139`):
- `getStartWatchResourceVersion`:
  - with `rev > 0`, it returns `rev`;
  - with WatchList on and SendInitialEvents false, it returns `getCurrentStorageRV`
    (`store.GetCurrentResourceVersion`, already specified and proved);
  - otherwise 0.
- `createWatchChan`:
  - two buffered channels: `incomingEventChan` (`*event`, 100) and `resultChan` (`watch.Event`,
    100);
  - `wc.ctx, wc.cancel = WithCancel(ctx)`;
  - two `blockLogger`s (a mutex, `clock.RealClock`, `klog.V(3)`).
- `go wc.run(...)`, then `utilflowcontrol.WatchInitialized(ctx)`. It returns `wc`, a
  `watch.Interface`.

**The goroutines of one watch:**
- **`run`**:
  - starts `startWatching` (counted in `resultChanWG`) and `processEvents`;
  - waits for `watchClosedCh` or `wc.ctx.Done()`;
  - then `cancel()`, `resultChanWG.Wait()`, and `close(resultChan)`.
  - So **`resultChan` is closed only after every producer has exited.**
- **`startWatching`** (the etcd side; the G1 function):
  1. If `initialRev > 0` and initial events are forced: `getCurrentStorageRV`, and a
     `TooLargeResourceVersion` error event if `initialRev` is above it.
  2. If forced, `sync()`:
     - with EtcdRangeStream off (7e's gate), `syncPaginated`: `client.KV.Get` of the key, or of
       the prefix range with `WithLimit(10000)`;
     - later pages are read `WithRev` the first page's revision, from `lastKey+"\x00"`;
     - every kv is queued as a synthetic create (`parseKV`);
     - `initialRev` becomes the first page's header revision.
  3. If the initial-events-end bookmark is required, it queues `progressNotifyEvent(initialRev)`
     annotated.
  4. `client.Watch(wc.ctx, key, WithRev(initialRev+1), WithPrevKV(), [WithPrefix])`.
  5. For each response:
     - `Err()`: `sendError`, then return;
     - a progress notification: a bookmark at the header revision;
     - otherwise each event goes through `parseEvent`, which errors on a non-create event without
       `PrevKv`, and is queued.
  6. When the client's channel closes: `close(watchClosedCh)`.
- **`processEvents`**:
  - With `ConcurrentWatchObjectDecode` **on (its default since 1.37)**:
    - a scheduler goroutine pairs each incoming event with a fresh response channel. It pushes
      that channel on `processingQueue` (capacity 9) and runs `transform` on a goroutine per
      event;
    - a collector goroutine pops the response channels in order and `sendEvent`s the results;
    - so the order is preserved.
  - With it off: one goroutine runs `transform` and `sendEvent` in order.
  - `transform` (`prepareObjs`: transformer, then `decodeObj` = `runtime.Decode`, then
    `versioner.UpdateObject(obj, rev)`):
    - a bookmark: `newFunc()` at the revision, annotated if it is the initial-events-end one;
    - a delete: the old object (at the delete's revision) if it passes the filter;
    - a create: the new object if it passes;
    - an update: Modified, Added or Deleted from the filter on the new and the old object
      (Modified if the predicate is empty).
  - A transform error: `sendError` from the processing goroutine, which then stops.

**The `ResultChan` contract** (what `store.Watch.spec` will say, §5.3; `nil` errors aside):
- the events received, without the Error events, are a prefix of the ideal stream:
  - (watch-list) the matching items in scope at some revision `r0 ≥ RV`, as Added in key order,
    then the annotated bookmark at `r0`;
  - then, for every revision `r > r0` (or `r > RV`) in order, the filtered event of the change at
    `r` if the key is in scope;
  - with bookmarks at progress points `p` that are at least the last event's revision and have no
    change in scope in between;
- at most two Error events (one per producer), **anywhere** in that prefix (§2.4);
- the channel closes after `Stop` (or the context's end) once the producers have exited.

**Bookmarks.**
- Only two kinds exist: the initial-events-end one (watch-list with AllowWatchBookmarks) and
  progress notifications.
- The store never asks for progress: `ProgressNotify` is false, set only by the cacher, and
  nothing calls `RequestWatchProgress` on these watches.
- But the client's `Watch` spec allows progress notifications whether asked for or not, so the
  contract allows them, and so does the check.
- AllowWatchBookmarks is otherwise ignored by etcd3.

**Compaction errors.**
- `ErrCompacted` from the client becomes `NewResourceExpired` (410) through
  `interpretWatchError`, as an Error event.
- The driver never compacts (7e §2), so 410 is unreachable. A nil `PrevKv`, which needs a
  compaction between the event and the server's `Range` at `rev-1`, is unreachable too.
- The check does not rely on either: an Error event of any kind is accepted.

**Resume.**
- The etcd3 watcher never resumes.
- The client's watcher resumes a broken gRPC stream on another endpoint from the last revision
  plus one. This is `watchGRPCStream.run`'s resume, already proved: `etcd_partition_watch_safe`
  resumes "at any member after a cut".
- A require-leader stream whose member has had no leader for 3 election timeouts is cancelled by
  the member (`monitorLeader`). The client then ends the watch with `ErrNoLeader`, and the etcd3
  watcher sends an Error event and closes.
- The driver's watcher then starts a new watch (the test's loop), possibly through another
  member: the "re-established after a blackhole" case of the plan.
- Seen in the prototype: the `noleader` schedule ends 19 watches with an Error event. The
  `blackhole` schedule has 11 `Watch` calls fail and later watches succeed through failover.

### 2.2 The configuration's gates

- **`WatchList`** must be on (the test sets it). With it off, a watch-list request gets no
  initial-events-end bookmark, and the validator rejects it. The driver calls
  `Set("WatchList=true")`. That needs a `featureOn` half of sweep repairs' B5 gate interface,
  which has only `featureOff` today (§6).
- **`EtcdRangeStream`** off, as in 7e: `sync` takes `syncPaginated`.
  `DefaultFeatureSupportChecker.Supports` is short-circuited and not called.
- **`ConcurrentWatchObjectDecode`**: on by default. Q7f-3: the serial path first, then the
  concurrent one.

### 2.3 What the watcher needs from etcd that no proof covers yet

1. **`WithPrevKV` through the watch stack.**
   - The client's `Watch` spec requires `prevKV = false` (`OpFull.isRangeWatch`,
     `Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1230`; `wrRO`'s `prevKV ↦□ false`,
     `client/v3/InvWatch.lean:844`).
   - The server's watch stream keeps its `prevKV` map empty (`swsMu`, `v3rpc/InvWatch.lean:318`,
     "the client asks for neither").
   - The send loop's `prevKV` branch (`v3rpc/watch.go:442-455`) is unproved. That branch is a
     `watchable.Range` at `ModRevision - 1` per non-create event, whose `KVs[0]` becomes the
     event's `PrevKv`.
   - Generalizing gives each event a `prevKv` that is none, or the key's kv at `rev - 1`. It is
     none only if that read failed, which is impossible without compaction.
2. **`WithRequireLeader`.** `store.watchContext` always adds the `hasleader` metadata.
   - The server's stream interceptor branch for it is excluded by the deployment premise
     `v3rpc.runsNoRequireLeader` (`v3rpc/InvStreamInterceptor.lean:76`).
   - That premise is in `etcdstart.commonPremises`, so in every etcd closed theorem and in the k8s
     ones.
   - The branch is excluded for two reasons (the same file's header):
     - (1) Perennial's `WithCancel` over a general parent does not relate the child's `Value` to
       the parent's, so `grpcRunCtx` does not carry over;
     - (2) `cancellableContext.Err()` returns its reason before `Done()` closes
       (`issues/etcd-stream-interceptor-err-before-done.md`), so the wrapper is not an
       `isContext`.
   - With the store's watches the premise is **false** for this driver, so 7f must prove the
     branch, `monitorLeader`'s cancellation over a non-empty `streams` map included. That map
     has interface keys; whether Perennial's map supports them is a risk to check in the Draft.
   - Then the premise can be deleted everywhere (§6, §7).
3. **The paginated `KV.Get`** of `syncPaginated`: `clientv3.KV.Get` with
   `WithRange`/`WithLimit` and `WithRev`. This is 7c-3's `Get` at a revision and 7e-1's range
   with a limit, called directly on `clientv3.KV`, not through `kubernetes.Client`. A
   non-recursive watch-list `Get`s one key at the latest revision (7c).
4. **Many concurrent watches on one client watcher**, each cancelled by its `wc.ctx`.
   `isClientWatcher` is persistent, and `run` multiplexes substreams. No example that this Scope
   checked runs more than one watch at a time on one watcher; the Draft checks that the spec
   allows it.

### 2.4 The watcher can deliver events after a `watch.Error` (a non-issue, with a test)

`sendError` (from `startWatching`'s goroutine) and `sendEvent` (from the processing goroutine)
race on `resultChan`:
- `sendError`'s `cancel()` runs only after its own send;
- `sendEvent`'s `select` may still pick the send once the context is cancelled.

So an Error event can come before decoded events of lower revisions. The watcher's own TODO
says so ("sendError doesn't guarantee that no more items will be put into resultChan").
- **Reproduced:** `TestErrorEventNotLast`, a fake `clientv3.Watcher` that sends 150 creates and
  then a compacted response, with a consumer that starts after 100 ms: 8 of 50 trials.
- **Consequence:** upstream's validator (Error last) and `runWatch` ("not closed after
  watch.Error") would fail on a correct run under partitions, so the theorem would be false.
- **The driver's check drops Error events wherever they occur** (§4.2). In
  `nonissues/k8s-etcd3-watcher-events-after-error.md`, `blocks-proof: yes`.
- Upstream was not searched (no `gh` here).

### 2.5 Two driver gaps the watcher exposes

- **`runtime.Decode(codec, data)` passes `into = nil`.** The driver's `codec.Decode` rejected it
  ("not an *Obj"), so every watch event failed to decode. The prototype allocates a new `Obj`.
  The codec contract (D30b, `contractOk`) gains decoding without a target.
- **The initial-events-end annotation** goes through `meta.Accessor(obj).SetAnnotations`, which
  the driver's `Obj` ignored. `Obj` gains an `Annotated` bit, false on every stored object
  (`GetAnnotations`/`SetAnnotations`).

## 3. G1, the Goose fix

- **Status: done.** Field selection through an alias (`getStructInfo` with `types.Unalias`)
  landed as Perennial `898c0ddc5` (`fix-semantics` Case 31). It has been pinned since 2026-11-04,
  and the compactor's `fromWatchResponse` uses it (`notes/perennial-changes.md`).
- **What is left is configuration:** drop `!parseEvent` and `!watchChan.startWatching` from
  `Code/k8s_io/apiserver/pkg/storage/etcd3.toml`.
  - Checked 2026-11-08 at the current Perennial pin `84d538063`
    (`etc/goose.py --project k8s-apiserver`, then reverted): both translate with bodies.
  - `Code/.../etcd3.lean` grows by 335 lines, and `GeneratedProof` is unchanged. Elaboration was
    not checked (no build in this stage).
- **The second alias limitation** (interface types whose methods name an alias stay axiomatized,
  `feature.FeatureSupportChecker`): it is not on the path. The `Supports` call is behind the
  EtcdRangeStream gate, which is off.
- **Names-only callees the translation reaches:**
  - `clientv3.Event.IsCreate`: add it to `client/v3.toml`'s list, a two-line body;
  - `WithPrevKV`: translate it as the other options;
  - `wait.Jitter`;
  - `utilflowcontrol.WatchInitialized`: `flowcontrol` is names-only; translate it and
    `initializationSignalFrom`, a `ctx.Value` lookup;
  - `klog.V(...).Enabled`/`InfoS`, `klog.Warningf`, and `metrics.RecordEtcdEvent`/
    `RecordEtcdBookmark`: no-op specs in the pattern of `klog.V`, `klog.Errorf` and
    `metrics.RecordEtcdRequest`, which exist.
- **The Perennial change 7f does need is not G1:**
  - **(P-RL1)** a general `WithCancel` spec over any `isContext` parent whose child's `Value` is
    the parent's;
  - it is needed for the require-leader branch (§2.3 2);
  - it is an independent change off Perennial's `lean`, about 150-250 Lean lines;
  - it goes into `notes/perennial-changes.md` (added by this Scope).

## 4. The design: watches as porcupine operations against the per-configuration history

### 4.1 Why not upstream's replay

Upstream replays the model along porcupine's linearization and validates every watch against
that replay's changes. That is sound only without failed writes (7d §2), and the driver keeps
failed writes pending. Two failure cases:
- **A late linearization point.** A failed write W that took effect at revision `r` may be
  linearized by porcupine after a successful write B at `r+1`. This is allowed when W's interval
  overlaps B's and nothing later reads W's key. Along that linearization no configuration has W
  at `r`, and a watch that saw W at `r` would be rejected on a correct run.
- **Shrinking W's interval does not help.** Recording W's return at its call still lets
  porcupine order an overlapping B first.

Rejected alternatives:
- (a) a gate that skips the watch check on any run with a failed write. Most partition runs
  would check nothing.
- (b) one final "check all watches" operation after all the others. This needs a lintest change
  too. Porcupine finds a failure only at the end, then backtracks over the whole history, and it
  needs a records table and a watcher pool outside lintest.

### 4.2 The design (prototyped)

- **A watch is one lintest operation of a watcher client.** `lintest.RunLin2`, new, runs a
  second group of clients with their own operation count. The watchers' `gen` draws a watch
  (`genWatch`).
- **`Apply` runs the whole watch** and returns its events (`Output.WEvents`), or `WFailed`.
- **Its linearization point is the watch's end.** At that point every event's revision is at most
  etcd's current revision, which the matching configuration's `hist` covers (7e's invariant
  `hist[R] = absK(stateAt R)`).
- **The model's step for a watch is `watchOk(in, out, c)`.** It keeps `c` when the events
  validate against `c.hist`, and drops it otherwise. A failed or skipped watch keeps `c`.
  Porcupine is complete, so on a real run the real linearization with the real configuration
  passes. This is the argument already used for 7e's past-revision lists: no replay is needed.
- **Watchers stop with the unary traffic**, as the test's do. `Gen` returns a `Skip` watch, which
  `Apply` answers at once, once the unary operations are done (a counter in the cache table).
  The operation counts stay fixed, as lintest needs.

**`watchOk`** is the validator ported to `c.hist`. The changes come from consecutive stores:
`changeAt(hist[r-1], hist[r])`, one key per revision ≥ 2, since every write is a single-key
transaction and revisions 2 and 3 are the seeds. It differs from upstream in four places, each
stated in its docstring:
1. **Error events are dropped wherever they occur** (§2.4), not required to be one and last.
2. **A watch-list that ended before its bookmark** must be a prefix of the initial events at
   some revision in `[max(RV,1), c.st.rv]`. Upstream rejects it ("missing initial events end
   bookmark"), but the consumer's timer can fire between the initial events and the bookmark.
3. **A `Watch` call that fails** (the client's error, e.g. `getCurrentStorageRV` during a
   blackhole) constrains nothing, like a failed read. Upstream's test panics.
4. **Every revision the events mark must be at most `c.st.rv`** (in place of upstream's
   "resource version not found in history"). The check reads `hist`, not upstream's `states`
   map.

As in 7b and 7e, the relative RVs are relative to the watcher's cached object, not to
`GetCurrentResourceVersion`.

**With partitions and failed writes:**
- each configuration carries its own history;
- a pending write that takes effect appends to that configuration's history at the revision
  where it does (7e);
- so a watch that saw a failed write's effect is accepted by the configurations where the write
  took effect at that revision.

A watch re-established on another member after a blackhole is a new operation of the same
watcher. Within one watch, the client's resume is invisible: the client spec says no gaps and no
duplicates.

## 5. The specs to write

### 5.1 etcd: client and server

- **`watcher.Watch.spec` (client), generalized.**
  - `isRangeWatch` gains `prevKV`.
  - `watchStateRespOk`'s events carry `prevKv`: none for a create, and otherwise none or the
    key's kv at `ev.rev - 1` (`stateAt`).
  - Callers that pass `prevKV = false` see no change: watchkv, cachekv, linkv3p's `MainWatch`,
    the compactor, `etcdstart.Collect`.
  - The context premise stays `watchCtx`. The require-leader metadata comes from
    `WithRequireLeader` (spec exists, `client/v3/WithRequireLeader.lean`) and travels in the
    stream's outgoing metadata (`streamKeyFromCtx`).
- **Server, `prevKV`.**
  - `swsMu` allows `prevKV` entries;
  - `recvLoop` records them (`creq.PrevKv`);
  - `sendLoop`'s branch: `watchable.Range` at `ModRevision - 1`, from the mvcc store's range at a
    revision (M2's `stateAt`);
  - the send-side contract (`rawRespOk`) gains `prevKv`.
- **Server, require-leader.**
  - `newStreamInterceptor`'s branch: `s.Leader()`, `ErrGRPCNoLeader`,
    `newCancellableContext`, `serverStreamWithCtx`, and the `streams` map insert and delete;
  - `monitorLeader`'s cancellation;
  - `cancellableContext.{Cancel,Err}`.
  - The handler's context:
    - **(RL-a)** a two-line etcd fork fix of the Err/Done order (`Cancel` closes `Done` before it
      publishes the reason; upstream-able, an issue exists). The wrapper is then an `isContext`
      given P-RL1;
    - **(RL-b)** no fork change. The watch handler takes a weaker context contract (`Done`, plus
      `Err` only after `Done`, the shape `watchCtx` already has on the client), which the issue
      says the handlers meet;
    - Q7f-2.
  - `runsNoRequireLeader` is then unused and deleted.

### 5.2 lintest

`RunLin2.spec`:
- `RunLin.spec` with a second group `(clients2, ops2)` and `clients + clients2 < 2^31`;
- `(clients·ops + clients2·ops2) < 2^60`;
- `gen` called with any id of either group;
- `RunLin` and `Run` keep their specs, proved from it, so no caller changes.

### 5.3 The store's watch

The vocabulary goes in `Proof/k8s_io/apiserver/pkg/storage/etcd3/WatchDefs.lean`, new:
- `idealStream L req r0 : List WEv` (pure, over the KV log `L`): the initial events and bookmark
  at `r0` (watch-list), then the filtered changes of `(r0, ∞)` in scope;
- `streamPrefixOk L req evs`: `evs`, without the errors, is a prefix of `idealStream L req r0`
  for some `r0`, with progress bookmarks allowed as in §2.1;
- `k8sWatch c wi γ req`: `wi`'s `ResultChan` returns an SPSC channel. After the consumer has
  received `evs`, it holds `□ streamPrefixOk (logLb γ) req evs`, where `logLb` is a persistent
  lower bound of etcd's log. `Stop` can be called.

The triple, sketched:

```lean
-- store.Watch.spec (sketch)
{{ storeOk c s ∗ watchReqOk c.S opts req ∗ watchCtx ctx cd ∗ featureOn g "WatchList" ∗ ... }}
  s.Watch(ctx, key, opts)
{{ (wi : GoInterface) (err : GoInterface), RET (wi, err);
     ⌜err ≠ nil⌝ ∨ (⌜err = nil⌝ ∗ ∃ γ, k8sWatch c wi γ req) }}
```

- `watchReqOk` holds when:
  - the key prepares;
  - the RV parses with the driver's versioner;
  - the predicate is the driver's (7e's selectors);
  - Limit is 0 and there is no Continue;
  - `RecordTimestamps` and `ProgressNotify` are false.
- Errors are not identified: the driver records any `Watch` error as `WFailed`.
- **Internal specs** (one per function, as for the store's other methods): the functions of
  §2.1, plus
  - `transformErrorToEvent`, `interpretWatchError`, `isCancelError`, `logWatchChannelErr`;
  - `blockLogger`'s `newBlockLogger`/`recordWait`;
  - `parseKV`, `progressNotifyEvent`, `prepareObjs`, `decodeObj`, `filter`, `acceptAll`;
  - for the concurrent path, `concurrentOrderedEventProcessing.{schedule,collect}EventProcessing`.
  - The protocol: `incomingEventChan` is an SPSC queue (the producer is `startWatching`, the
    consumer is processing) whose elements carry the ideal stream's next item. `resultChan` has
    two producers (`sendEvent` in order; `sendError`, which carries nothing).

### 5.4 The driver

- **New functions, each with its spec:**
  - `genWatch`: any watch input with `inOk`;
  - `watchOptions`, `toWEvent`, `lastObj`;
  - `runWatch`: its output's events satisfy `streamPrefixOk` for the input's request, or it is
    `WFailed`;
  - `Apply`'s `KWatch` branch, logically atomic, linearized at the end;
  - `watchOk` and its pieces as Go functions proved equal to the pure `watchOkL`.
- **`Gen`, `Apply` and `Check`** (Check calls `RunLin2`) change.
- **`Main`, `MainCluster` and `MainPartition`** gain `watchers, wops` (Q7f-1).
- **The obligation behind the theorem** is a pure Lean lemma, `watchOkL_of_stream`:
  - Premises: kInv's `hist[R] = absK (stateAt L R)` for `1 ≤ R ≤ cur`, `streamPrefixOk L req
    evs`, and every revision in `evs` at most `cur`.
  - Conclusion: `watchOkL in out c` for the matching configuration.
  - It needs `absK` to commute with `changeAt` (one key per revision) and with the predicate's
    filtering.
- **The codec's contract** gains decoding without a target. `Obj`'s metav1 accessors gain the
  annotation.

## 6. New trusted text and premises, with their producers

| Item | Kind | Producer |
| --- | --- | --- |
| `watchOk` and its helpers (the Go copy of `WatchValidator`, specialized; four departures, §4.2) | trusted checker text (D30m, as `Model`) | this stage; replaced by the maintainers' `WatchValidator` in 7g, as a refinement |
| `featureOn g "WatchList"` from `Set("WatchList=true")` | gate fact | sweep repairs 1's B5 interface, extended with the `true` half (one joint restatement, as for 7e's `featureOff`); `axiom` skill before use |
| `ConcurrentWatchObjectDecode`'s value | gate fact | the same, `Set` to `false` for 7f-5a; the default on for 7f-5b (Q7f-3) |
| `wait.Jitter` | local trust-boundary spec ("some duration") or translation | 7f-5 Draft; `axiom` skill |
| `clientv3.Event.IsCreate`, `WithPrevKV`, `utilflowcontrol.WatchInitialized` | translations (configuration), no trust | 7f-5 |
| `klog.V` and `klog.Errorf` (specs exist); `Verbose.Enabled`, `Verbose.InfoS`, `klog.Warningf`, `metrics.RecordEtcdEvent`/`RecordEtcdBookmark` (`RecordEtcdRequest`'s exists); `clock.RealClock.Now` (exists) | no-op specs in the existing pattern (reused, or new ones like `RecordEtcdRequest`'s), each listed in 7f-5a's Draft | 7f-5a |
| P-RL1: `WithCancel`'s child `Value` is the parent's | Perennial spec (general, proved in Perennial) | independent Perennial change |
| RL-a only: the `cancellableContext` Err/Done order | etcd fork fix | Q7f-2 |
| `v3rpc.runsNoRequireLeader` | **removed** premise (deployment) | deleted once 7f-4 proves the branch |
| watcher bounds: `watchers·wops` and the goroutines per watch under adequacy's thread bound | adequacy constants | the grpc serve pool's stage B (thread-token pool) |

No `Assumptions` class is added if the watcher's apimachinery callees are translated (`meta.Accessor`
since 7b, `apierrors.NewInternalError`/`NewResourceExpired`, `APIStatus.Status`) or covered by the
store's existing local specs. The Draft lists each one.

## 7. The closed theorems that change

**Programs and statements change:**
- `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe` and `k8s_etcd3_partition_safe`, with
  `k8setcd3_Main`, `k8setcd3_MainCluster` and `k8setcd3_MainPartition`;
- `Main*` gain `watchers, wops`, with bound premises on them (Q7f-1);
- `Check` calls `RunLin2`.

**A premise is deleted** (a strengthening, but the statements change). These carry
`runsNoRequireLeader` through `etcdstart.commonPremises` or their own Defs:
- `etcd_putget_safe`, `etcd_putget3_safe`, `etcd_txnlin_safe`, `etcd_watch_safe`;
- `etcd_partition_safe`, `etcd_partition_watch_safe`;
- auth, lease, leasegrant, leaseexpiry, compacted, compactwatch;
- `k8s_compactor_safe`, `k8s_compactor_partition_safe`;
- the three k8s etcd3 theorems.

The Draft regenerates the exact list (`etc/importers.py --uses runsNoRequireLeader`).

**Re-proved, statements unchanged:**
- every user of the client's `watcher.Watch.spec` (its `prevKV`-false instances);
- the v3rpc watch proofs (`serverWatchStream__{recvLoop,sendLoop}`, `watchServer__Watch`);
- the stream interceptor's;
- lintest's `Run`/`RunLin` callers: none re-proved, since their specs are kept.

**Interface files:**
- raft's API is untouched;
- `etcdstart`'s interface files change if `commonPremises` does
  (`interface/Proof/.../lib/etcdstart/*.txt`).
- Each Draft shows the diff.

**Vacuity**, as for 7e: until the per-type landing (`pbEnc_ok`), sweep repairs 1 and the grpc serve
pool's fix, these theorems are vacuous or rest on false axioms. 7f's value arrives with them.

## 8. The Go prototype

`notes/k8s-7f-proto.patch` applies to `k8s-7e` (`736463a4bd`). Six files, 1177 patch lines:

| File | Contents |
| --- | --- |
| `examples/lib/lintest/lintest.go` | `RunLin2` |
| `examples/k8s/etcd3/watch.go` | `genWatch`, `runWatch`, `watchOk` and its helpers |
| `examples/k8s/etcd3/watchmain.go` | `CheckW`, `MainW`, `MainPartitionW` |
| `examples/k8s/etcd3/k8setcd3.go` | `Obj.Annotated`, `Input`/`Output` watch fields, the step's `KWatch` branch, `Gen`/`Apply`, the codec's nil target |
| `examples/k8s/etcd3/watch_test.go` | the tests below |
| `examples/k8s/etcd3/errorder_test.go` | §2.4 |

The prototype keeps today's `Main*` and adds `*W` variants. Q7f-1 decides the final shape.

**Runs**, each test in its own process, all under `systemd-run -p MemoryMax=32G`, `GOWORK=off`:

| Test | Configuration | Result |
| --- | --- | --- |
| `TestMainWatch` | one member; 8 unary clients × 300, 16 watchers × 8 | `Ok`, 2 of 2 runs, about 4 s, peak RSS 96 MB. About 37 watches (all four behaviours), 22-26 with events, 12-14 watch-lists with events. Per run: about 600 Added, 300-550 Modified, about 600 Deleted, 12-14 initial-events bookmarks. Revisions up to 544. |
| `TestWatchCorrupt` | one member; 4 × 60, 8 × 6; the first watch with a change event corrupted | `Illegal` for each of `value` (the object's value), `rv` (its resource version), `type`, `drop` (an event not the last) and `dup` (an event duplicated); 1.8-3.7 s each |
| `TestMainPartitionWatch` | three members; 4 × 60, 8 × 12; schedules `isolate`, `election`, `blackhole`, `drop`, `mixed` (7c's) and `noleader` (new: every peer link cut for 6 s) | **`Ok` in 30 of 30 runs** (5 rounds × 6 schedules); peak RSS 73-90 MB; 0.5-15 s each. The runs reach failed unary writes (1-3 per run), failed `Watch` calls (up to 16) and Error events (`noleader`: 19 watches end with one). |
| `TestErrorEventNotLast` | fake client watcher | an Error before later events in 8 of 50 trials (§2.4) |

The existing tests still pass (`TestMainLinearizable`, `TestModel*`, `TestList*`,
`TestMainCluster`, lintest's).

Not tested:
- the concurrent decode on and off separately (the default, on, was used);
- dropping the **last** event, which no check can see (upstream neither): the range shrinks with
  it.
- An `Error` event after an initial event in the `noleader` runs did not occur. §2.4's test covers
  that ordering.

## 9. Stages, estimates, dependencies

| Stage | Contents | Lean lines | Depends on |
| --- | --- | --- | --- |
| 7f-0 | Go: the prototype made the driver (Q7f-1's shape), the codec's nil target, `Obj.Annotated`, the gates (`WatchList` on, `ConcurrentWatchObjectDecode`), mode-count tests as 7e's `TestTrafficReachesCases`, 5×6 partition runs | Go only (~900 lines) | 7e-0 (landed on `k8s-7e`) |
| 7f-1 | `lintest.RunLin2` spec and proof; `Run`/`RunLin` re-derived | 200-400 | none |
| 7f-2 | pure: `WEvent`, `watchOkL`, `changeAtL`, `toEventL`, `initialEventsL`, `stepL`'s `KWatch`, and the crux `watchOkL_of_stream` (§5.4) | 1200-2000 | 7e-3a/3b (the `hist` model) |
| 7f-3 | `WithPrevKV` through the watch stack: client spec and proofs (`isRangeWatch`, `watchStateRespOk`), server `recvLoop`/`sendLoop`/`swsMu`, `WithPrevKV`'s translation | 1500-2500 | per-type landing (InvProto/InvGrpc rewrite) |
| 7f-4 | require-leader streams: the interceptor branch, `monitorLeader`, `cancellableContext`, `serverStreamWithCtx` (Q7f-2), the interface-keyed map; `runsNoRequireLeader` deleted from every theorem; plus P-RL1 in Perennial (150-250) | 1500-2500 | per-type landing; P-RL1 landed and pinned; grpc serve pool stage B (streams count against the handler pool) |
| 7f-5a | the etcd3 watcher, serial decode: the configuration (G1 exclusions dropped, `IsCreate`, `WatchInitialized`), `store.Watch.spec` and `k8sWatch`, `watcher.Watch`, `run`, `startWatching`, `sync`/`syncPaginated`, `serialProcessEvents`, `transform`..., the trust specs (Draft) | 3000-4500 | 7f-3, 7f-4; 7c-3 and 7e-1 (the paginated `Get`); sweep repairs B5 (`featureOn`) |
| 7f-5b | the concurrent decode path (scheduler, collector, per-event goroutines; ordered SPSC of response channels) | 800-1200 | 7f-5a |
| 7f-6 | the driver: `genWatch`, `runWatch`, `Apply`/`Gen`/`Check`, `Main*`, the codec contract re-proved, adequacy, the three closed theorems | 2000-3000 | 7f-1, 7f-2, 7f-5; stage B (adequacy's thread bound) |
| total | | 10200-16100 | |

**The order.**
- 7f-0, 7f-1 and 7f-2 start at once: they are independent of the in-flight work.
- 7f-3 and 7f-4 come after the per-type landing. They are etcd-side and benefit every watch
  example.
- 7f-5a after them, with 7c-3 and 7e-1 in. Then 7f-6 on 7f-5a's spec, and 7f-5b last (it changes
  no statement).

**Checkpoints** (each a report to 81):
1. 7f-0's Go report.
2. 7f-2 built.
3. 7f-3's statements (the client spec's change).
4. 7f-4's Draft (the premise deletion, P-RL1, Q7f-2's choice: a hard stop).
5. 7f-5a's Draft (`store.Watch.spec`, `k8sWatch`, the trust specs: a hard stop).
6. 7f-6's Freeze package.

**7g** then translates the maintainers' `WatchValidator` (with `Replay`). As in 7e §10, its check
on runs with no failed write is a refinement of ours, except §4.2's departures 1-2. There it is
stricter, so it would fail on the runs §2.4 describes. 7g must keep our check where they differ,
or wait for an upstream fix of the watcher.

## 10. Questions for 81

- **Q7f-1. The entry points.** (a) Extend `Main`, `MainCluster` and `MainPartition` with
  `watchers, wops`: one set of theorems, with 0 watchers the old program. (b) Keep them and add
  `Main*W` with three more theorems. **Recommended: (a)**: the driver is `TestCorrectness`'s
  analogue, and watches are part of it.
- **Q7f-2. The require-leader handler context.** (RL-a) a two-line etcd fork fix of
  `cancellableContext`'s Err/Done order, with P-RL1. (RL-b) no fork change, and a weaker context
  contract for the watch handler. **Recommended: (RL-b)** if the Draft confirms that the watch
  and lease handlers read `Err()` only after `Done()`, since it verifies etcd as shipped; (RL-a)
  otherwise.
- **Q7f-3. `ConcurrentWatchObjectDecode`.** **Recommended:** serial first (7f-5a, the gate set
  off), then the default, concurrent (7f-5b), which is how Kubernetes runs. The final theorems are
  at the default.
- **Q7f-4. The departures from upstream's validator** (§4.2: errors anywhere, a truncated
  watch-list, a failed `Watch` call, cached-relative RVs). **Recommended:** accept them as stated.
  The first is forced by §2.4, the second by the consumer's timer, and the third by partitions.
- **Q7f-5. The non-issue** (§2.4): record it in `nonissues/` as written (this branch), and leave
  an upstream report to the user. **Recommended: yes.**
