# k8s etcd3 stage 7f, watches: Scope, revision 2 (2026-11-08, branch `k8s-7f`; to etcd-grove-81)

**Changes from revision 1.** They answer the review (`/shared/tmp/k8s-7f-scope-review.md`,
wf_25ef97ea-de4: "revise, then approve; the core design holds") and carry these decisions:
- **The user (2026-11-08):**
  - accept departures 1-4 from upstream's validator, on two conditions: every bookmark is bounded
    by `c.st.rv`, and events with a foreign object are rejected (`WBad`), not dropped. Both are
    now in the prototype (§4.2);
  - **delete `runsNoRequireLeader`, with no etcd fork change** (§2.3, §5.1).
- **81:**
  - Q7f-1 (a): `Main`, `MainCluster` and `MainPartition` gain `watchers, wops`. Done in the
    prototype;
  - Q7f-2: neither RL-a nor RL-b, but a weak handler-context contract, a changed grpc
    stream-interceptor contract (with a reviewed `incomingOf` fact), and Watch **and**
    LeaseKeepAlive re-proved over it (§5.1). 7f-4 is re-estimated (§9);
  - P-RL1 restated (§3);
  - Q7f-3: both values of `ConcurrentWatchObjectDecode`, serial first, so no gate fact for it;
  - Q7f-5: yes, with the non-issue's front matter fixed (upstream not searched) and its rate
    (1-12 of 50).
- **The review's other fixes:**
  - the flaky drop corruption (it now drops a middle event, and a `none` corruption must be Ok);
  - the missing callees and trust items: `WithRequireLeader` over a caller's context,
    `runtime.Decode`, `getResourceSizeEstimator`/`collectorMux`, `errors.As`, and more (§3, §6);
  - `Output.WEvents` as a plain encoded value, as 7e's `Items` (`encodeWEvents`, §4.2);
  - `changeAt` made deterministic (a merge of the key-sorted items);
  - `RunLin` now calls `RunLin2`;
  - a Goose dry run of the prototype (§8);
  - the prototype rebased on `k8s-7e` `7f2ad6c9b5` (7e's `90b6252aa5` already folded in the codec's
    nil target and `Obj.Annotated`);
  - the dependencies on 7e-4 and 7e's object layer (§9);
  - the departures put in two lists: the validator's, and the traffic's (§4.2).

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
(`7f2ad6c9b5`): the driver's watch traffic and check, the entry points with watchers, and
`lintest.RunLin2`.
- It passes on real runs: one member, and six partition schedules × 5 runs, all under the 32G cap.
- Porcupine rejects five kinds of corrupted watch event (drop now a middle one), and accepts an
  uncorrupted one, in every run (§8).
- It translates with the pinned Goose (dry run, not elaborated).

**Three findings shape the stage:**
1. **The validator, as upstream writes it, would make the closed theorem false.** The etcd3
   watcher can deliver events after a `watch.Error` event (§2.4,
   `nonissues/k8s-etcd3-watcher-events-after-error.md`, reproduced in 1-12 of 50 trials over
   several runs). A correct run could fail upstream's check, so the proof must accept it.
2. **Replaying the validator along porcupine's linearization is unsound once failed writes are
   allowed.** This is 7d §2's trap. So watches become porcupine operations, checked against each
   configuration's history (7e's `hist`) (§4).
3. **The store's watches use two etcd paths that no proof covers yet: `WithPrevKV` and
   `WithRequireLeader`** (§2.3). The second makes the deployment premise
   `v3rpc.runsNoRequireLeader` false for this driver, and that premise is in every etcd closed
   theorem. Deleting it changes grpc's stream-interceptor contract and the context every stream
   handler runs under (Watch and LeaseKeepAlive). G1 itself needs no more Goose work: its fix
   landed (Perennial `898c0ddc5`, §3); the watcher's other callees do (§3).

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
- Seen in the prototype (revision 1's runs; revision 2's are in §8): the `noleader` schedule ends 19 watches with an Error event. The
  `blackhole` schedule has 11 `Watch` calls fail and later watches succeed through failover.

### 2.2 The configuration's gates

- **`WatchList`** must be on (the test sets it). With it off, a watch-list request gets no
  initial-events-end bookmark, and the validator rejects it. The driver calls
  `Set("WatchList=true")`. That needs a `featureOn` half of sweep repairs' B5 gate interface,
  which has only `featureOff` today (§6).
- **`EtcdRangeStream`** off, as in 7e: `sync` takes `syncPaginated`.
  `DefaultFeatureSupportChecker.Supports` is short-circuited and not called.
- **`ConcurrentWatchObjectDecode`**: on by default. Decided (Q7f-3, 81): `processEvents` is
  proved for **both** values of `Enabled`, so this feature needs no gate fact. The serial branch
  comes first (7f-5a, the concurrent branch out of scope there), then the concurrent one (7f-5b).

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
2. **`WithRequireLeader`.** `store.watchContext` always adds the `hasleader` metadata
   (`store.go:1151, 1162`).
   - **The client side.** `WithRequireLeader` is names-only (grpc's `metadata`), and its one spec
     covers only `WithRequireLeader(context.Background())` (`client/v3/WithRequireLeader.lean`, the
     lease client's stop context). The store calls it on the caller's context, a `WithTimeout`
     context in the driver. So a new trust-boundary triple is needed: over a `watchCtx` parent,
     the result is a `watchCtx` with the parent's `Done`/`Err`, whose outgoing metadata is the
     parent's plus `hasleader: ["true"]` (§6). The unary require-leader branch, which
     `getCurrentStorageRV` and `syncPaginated` reach with the same context, is already proved for
     any metadata (`newUnaryInterceptor.spec`).
   - **The server side.** The stream interceptor's require-leader branch is excluded by the
     deployment premise `v3rpc.runsNoRequireLeader` (`v3rpc/InvStreamInterceptor.lean:76`), which
     is in `etcdstart.commonPremises` (26 files), so in every etcd closed theorem and the k8s ones.
     With the store's watches the premise is **false** for this driver.
   - **Decided (the user, 2026-11-08): delete the premise, with no etcd fork change.** What
     that takes (the review's findings, 81's decisions on Q7f-2):
     - **No option makes the wrapper an `isContext`.** After `monitorLeader`'s
       `Cancel(rpctypes.ErrGRPCNoLeader)`, `cancellableContext.Err` returns that gRPC status error,
       and Perennial's `isContext` allows only `Canceled` or `DeadlineExceeded` (`isCtxErr`,
       Perennial `Proof/context/Base.lean:212-217`). The Err-before-Done window
       (`issues/etcd-stream-interceptor-err-before-done.md`) is only the second obstacle.
     - **A weak handler-context contract** (`srvCtxWeak ci' cd`): `Done()` as `isContext`'s;
       `Err()` at any time is nil or some error; once `Done` is closed, `Err()` is non-nil and
       either `isCtxErr` or `ErrGRPCNoLeader` (a status error `srvErrOk` describes). `isContext`
       implies it, so the branch without require-leader still passes `ci`.
     - **grpc's stream-interceptor contract changes** (`srvStreamInterceptorOk`,
       `Proof/google_golang_org/grpc/InvGrpcStream.lean:723-742`). Today the interceptor "calls h
       with the same context ci". It becomes: it calls `h` with a stream whose context `ci'`
       satisfies the weak contract and has the same incoming metadata,
       `metadata.incomingOf ci' = metadata.incomingOf ci`. That equality is a reviewed
       trust-boundary fact (grpc's `metadata` keys live in grpc's value chain, which `WithCancel`
       passes through; `incomingOf` is opaque, `grpc/metadata/Incoming.lean:27`), attacked with
       the `axiom` skill. `grpcStreamHandlerOk`'s metadata-indexed `Spec` (`:674-680`) then reads
       the same metadata.
     - **Every stream handler is re-proved over the weak context:**
       - Watch: `watchServer__Watch`, `serverWatchStream__{recvLoop,sendLoop,isWatchPermitted}`,
         about 3400 lines today;
       - LeaseKeepAlive: `LeaseServer__LeaseKeepAlive`, `leaseKeepAlive`, about 440 lines;
       - where they read the context, checked one by one in the 7f-4 Draft:
         - the `select` on `Done`;
         - the reads of `stream.Context().Err()` after a `Recv`/`Send` error, while `Done` may
           be open (`watch.go:203, 492, 550, 574`, `lease.go:118, 149`; only for the log level
           and the `streamFailures` metric);
         - `errors.Is(err, context.Canceled)` on the returned error;
         - the derived contexts: `traceutil.Tracer.Start(stream.Context())` (`watch.go:333`),
           `AuthInfoFromCtx` (`watch.go:240`), and `LeaseRenew(stream.Context())`, which runs
           `Tracer.Start` and then `context.WithTimeout(ctx)` (`v3_server.go:490, 535`).
           `WithTimeout`'s `propagateCancel` over a parent that is not an `isContext` needs a
           derivation lemma for the weak contract (P-RL2, §3).
     - **The branch itself:**
       - `s.Leader()` and `ErrGRPCNoLeader`;
       - `newCancellableContext` (`WithCancel` of the stream's context), `Cancel` and `Err`
         under the `RWMutex`;
       - `serverStreamWithCtx.Context`;
       - the `streams` map insert and the deferred delete and `Cancel(nil)`;
       - `monitorLeader`'s loop over a now non-empty map (`streamsMapInv` generalized). Each
         entry's `Cancel(ErrGRPCNoLeader)` is followed by `<-ss.Context().Done()`. The map is
         keyed by interface values (a `serverStreamWithCtx` in an interface); that Perennial's
         map supports such keys is a risk to check first.
     - **Then `runsNoRequireLeader` is deleted** everywhere (§7).
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
  then a compacted response, with a consumer that starts after 100 ms. Across several runs (ours
  and the reviewers'): 1 to 12 of 50 trials.
- **Consequence:** upstream's validator (Error last) and `runWatch` ("not closed after
  watch.Error") could fail on a correct run, so the proof must accept such runs. It was not seen
  in the driver's 30 partition runs: an `ErrNoLeader` cancel comes 3 election timeouts after the
  member loses its leader, when a decode backlog is unlikely.
- It also makes departure 2 (§4.2) necessary beyond the consumer's timer. Initial events, then an
  Error, then a close with no bookmark is possible (the processing goroutine stops on `Done`
  before it sends the queued bookmark).
- **The driver's check drops Error events wherever they occur** (§4.2). In
  `nonissues/k8s-etcd3-watcher-events-after-error.md`, `blocks-proof: yes`.
- Upstream was not searched (no `gh` here); the non-issue says so.

### 2.5 Two driver gaps the watcher exposes (folded into 7e)

- **`runtime.Decode(codec, data)` passes `into = nil`.** The driver's `codec.Decode` rejected it
  ("not an *Obj"), so every watch event failed to decode.
- **The initial-events-end annotation** goes through `meta.Accessor(obj).SetAnnotations`, which
  the driver's `Obj` ignored.

Both are fixed on `k8s-7e` (`90b6252aa5`): a new `Obj` when there is no target, and
`Obj.Annotated`, never encoded. 7e's object layer is on the 8-field `Obj`. The codec contract's
decode without a target is 7e's (§9).

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
- **So G1's part is configuration, but the watcher's callees are not.** What the translation
  reaches that is names-only, untranslated or new to the proofs (the review's list completed):
  - `clientv3.Event.IsCreate`: add it to `client/v3.toml`'s list (a two-line body);
  - `clientv3.WithPrevKV`: translate it, as the other options;
  - `clientv3.WithRequireLeader` over a caller's context: names-only (grpc `metadata`), a new
    trust-boundary triple (§2.3 2, §6);
  - `runtime.Decode` (`decodeObj`, every watch event): names-only (`runtime.toml` translates
    only `Encode` and `SetZeroValue`). Translate it: it is `d.Decode(data, nil, nil)`, which
    lands on the driver's codec, whose decode without a target is in 7e's contract;
  - `store.getResourceSizeEstimator` (`startWatching`, `store.go:279-282`): translated, but it
    takes `collectorMux.RLock`, a reader slot under the bounds plan. It needs:
    - a spec with a reader slot;
    - an entry in `etc/bounds-*.txt`;
    - a store invariant that the estimator stays nil. The driver never calls
      `EnableResourceSizeEstimation`, so `UpdateKey`/`DeleteKey` are unreachable;
  - `errors.As` in `interpretWatchError` and `transformIfCorruptObjectError` (`errors.go:37-38`,
    reached on every Error event): Perennial's `errors.As` spec (`Proof/errors/As.lean`) over the
    error types involved (`*corruptObjectDeletedError`, `*corruptObjectError`);
  - `fmt.Errorf` with `%q`/`%d`/`%s` and `mvccpb.Event_EventType.String` (`parseEvent`'s
    nil-`PrevKv` error): reachable under the client spec (`prevKv` none). Perennial's
    `fmt.Errorf` spec covers `ArgWf` arguments; `%q` of a string is checked in the Draft;
  - `fatalOnDecodeError.Load()` (a package `atomic.Bool`, from `KUBE_PANIC_WATCH_DECODE_ERROR`,
    already in `Init.lean`). `decodeObj`'s panic branch is unreachable because every stored
    value decodes (the store invariant), whatever the variable says;
  - `storage.AnnotateInitialEventsEndBookmark` (translated; `meta.Accessor`, a map built and
    read through the driver's `Get`/`SetAnnotations`);
  - `apierrors.NewInternalError`, `NewResourceExpired` and the `APIStatus` type assertion in
    `transformErrorToEvent`: translations if apimachinery's `errors` bodies are in, else local
    specs (Draft);
  - `wait.Jitter` (a random duration);
  - `utilflowcontrol.WatchInitialized`: `flowcontrol` is names-only; translate it and
    `initializationSignalFrom`, a `ctx.Value` lookup with no signal in the driver's context;
  - `klog.V(...).Enabled`/`InfoS`, `klog.Warningf`, `metrics.RecordEtcdEvent`/
    `RecordEtcdBookmark`: no-op specs in the pattern of `klog.V`, `klog.Errorf` and
    `metrics.RecordEtcdRequest`, which exist; `clock.RealClock.Now` exists.
- **Perennial changes 7f-4 may need** (none is G1; each is decided in the 7f-4 Draft and, if
  kept, is an independent change off Perennial's `lean`):
  - **(P-RL1, restated)** For a key `k ≠ cancelCtxKeyAny`:
    `(WP parent.Value(k) {Φ}) -∗ WP child.Value(k) {Φ}`, for `child = WithCancel(parent)`.
    - Its premise: the parent's dynamic type is not one of the types Go's `context.value` reads
      the fields of directly instead of calling `Value`, namely `*valueCtx`, `*timerCtx` and
      `withoutCancelCtx` (`src/context/context.go`'s `value`). Or else a persistent description
      of such a parent's fields.
    - As first phrased ("the child's `Value` is the parent's") it was false. For
      `&cancelCtxKey` the child returns itself, and grpc's real stream context is a `*valueCtx`
      chain.
    - `wp_WithCancel_any` already keeps the `ContextDesc` (Perennial `Results.lean:208-216`).
    - **The handler needs only the `incomingOf` equality above, which is a fact here, not a
      Perennial law.** So P-RL1 may be unnecessary. The Draft decides, after checking what the
      grpc model's `ci` is.
  - **(P-RL2)** Context derivations over a parent with the weak contract: `WithValue` (for
    `Tracer.Start`) and `WithTimeout`/`WithCancel` (`LeaseRenew`) give a child with the weak
    contract. Go's child takes `parent.Err()` on the parent's cancellation, so `ErrGRPCNoLeader`
    propagates. Its natural form generalizes `isContext` over the predicate its errors satisfy.
    This is general; it is stated in the 7f-4 Draft and recorded in `notes/perennial-changes.md`
    then.

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
- **`Apply` runs the whole watch** and returns its events, or `WFailed`. `Output.WEvents` is a
  plain encoded value (`encodeWEvents`: per event, its type and annotation bytes, its object's
  resource version, its encoding's length and `encodeObj`), as 7e's `Output.Items`, so `Output`
  stays a value porcupine's model decodes purely. The model decodes it (`decodeWEvents`); its Lean
  side reuses `encItemsL`'s injectivity (from the codec's round trip).
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
`changeAt(hist[r-1], hist[r])`, a merge of the two key-sorted item lists that returns the first
key that differs (deterministic; one key per revision ≥ 2, since every write is a single-key
transaction and revisions 2 and 3 are the seeds; 7f-2 states that as a lemma over the
histories the model reaches, pending writes included).

**Departures from upstream's validator** (accepted by the user, 2026-11-08, on the two
conditions marked; each stated in `watchOk`'s docstring):
1. **Error events are dropped wherever they occur** (§2.4), not required to be one and last.
   Only a genuine `watch.Error` with a `*metav1.Status` of status `Failure` is an Error event
   (`WError`).
2. **A watch-list that ended before its bookmark** must be a prefix of the initial events at
   some revision in `[max(RV,1), c.st.rv]`. Upstream rejects it ("missing initial events end
   bookmark"). The consumer's timer can fire between the initial events and the bookmark, and an
   Error can cut the stream there (§2.4).
3. **A `Watch` call that fails** (the client's error, e.g. `getCurrentStorageRV` during a
   blackhole) constrains nothing, like a failed read. Upstream's test panics.
4. **Every revision an event carries, bookmarks' included, is at most `c.st.rv`** (in place of
   upstream's "resource version not found in history"). **Condition: bookmarks are bounded by
   `c.st.rv`** (revision 1 accepted a progress bookmark at `c.st.rv + 1`; now checked directly).

And, **the second condition**, a strengthening over revision 1: **an event with a foreign object
is rejected** (`WBad`), not dropped. A foreign object is an Added, Modified, Deleted or Bookmark
event whose object is not the driver's `*Obj`, or an Error event without a `Failure` status.

What no check sees (as upstream's validator):
- a dropped last event of any watch;
- a dropped first (or only) event of a watch whose window the request does not pin (RV `""` or
  `"0"` without a watch-list: the window starts at the first event).

`TestWatchOkEdges` shows both, and the corruption test drops a middle event (§8).

**Departures of the traffic and the consumer from the test** (not the validator's):
- the relative RVs are relative to the watcher's cached object, not to
  `GetCurrentResourceVersion` (as 7b's and 7e's);
- with no cached object, the RV is drawn among the three that need none (`""`, `0`, `1`), where the
  test skips the request and draws again;
- after a `watch.Error` the consumer keeps reading until the channel closes or its time is up (the
  test reads once more and reports an error if the channel is open);
- a failed `Watch` call is recorded (the test panics);
- the test's pacing is kept: a watch shorter than `HiccupDuration` is followed by a sleep for the
  rest (revision 1 dropped it).

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
  - The context premise stays `watchCtx`. The watch's context is
    `wc.ctx = WithCancel(WithRequireLeader(ctx))`: the new `WithRequireLeader` triple over a
    `watchCtx` parent (§6) gives a `watchCtx` with `hasleader` in its outgoing metadata, and
    `WithCancel` over it gives one again. The stream key comes from `streamKeyFromCtx`, whose
    spec is generic in the metadata.
- **Server, `prevKV`.**
  - `swsMu` allows `prevKV` entries;
  - `recvLoop` records them (`creq.PrevKv`);
  - `sendLoop`'s branch: `watchable.Range` at `ModRevision - 1`, from the mvcc store's range at a
    revision (M2's `stateAt`);
  - the send-side contract (`rawRespOk`) gains `prevKv`.
- **grpc, the stream-interceptor contract.** `srvStreamInterceptorOk`
  (`InvGrpcStream.lean:723-742`) changes: the handler is called with a stream whose context `ci'`
  satisfies the weak contract `srvCtxWeak` and has `metadata.incomingOf ci' = metadata.incomingOf
  ci` (the reviewed fact, §6), instead of the same `ci`. `grpcStreamHandlerOk` and the stream
  handlers' triples take `srvCtxWeak` in place of `isContext ∗ grpcRunCtx` where the handler
  needs only that. The interceptors that pass `ss` unchanged (grpc-prometheus, the
  non-require-leader branch) meet it from `isContext`.
- **Server, require-leader** (§2.3 2):
  - `newStreamInterceptor`'s branch: `s.Leader()`, `ErrGRPCNoLeader`,
    `newCancellableContext`, `serverStreamWithCtx.Context`, and the `streams` map insert and the
    deferred delete and `Cancel(nil)`;
  - `cancellableContext.{Cancel,Err}` under its `RWMutex`, giving `srvCtxWeak`;
  - `monitorLeader`'s cancellation over a non-empty map (`streamsMapInv` generalized: each entry
    a `serverStreamWithCtx` whose `cancellableContext` the map's invariant can cancel);
  - the handlers re-proved over `srvCtxWeak`:
    - Watch: `watchServer__Watch` and `serverWatchStream__{recvLoop,sendLoop,isWatchPermitted}`;
    - LeaseKeepAlive: `LeaseServer__LeaseKeepAlive` and `LeaseServer__leaseKeepAlive`;
    - with the derived contexts (`Tracer.Start`, `AuthInfoFromCtx`, `LeaseRenew`'s
      `WithTimeout`) through P-RL2 or local lemmas;
  - `runsNoRequireLeader` is then unused and deleted (no etcd fork change: the user's decision).

### 5.2 lintest

`RunLin2.spec`:
- `RunLin.spec` with a second group `(clients2, ops2)` and `clients + clients2 < 2^31`;
- `(clients·ops + clients2·ops2) < 2^60`;
- `gen` called with any id of either group;
- `RunLin`'s body is now `return RunLin2(model, apply, gen, clock, clients, ops, 0, 0,
  timeout)` (in the prototype), so `RunLin.spec` and `Run.spec` are proved from `RunLin2.spec`
  and no caller changes. The translation of `RunLin` changes; its spec does not.

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
  - `store.getResourceSizeEstimator` (a reader slot of `collectorMux`; the estimator nil);
  - for the concurrent path, `concurrentOrderedEventProcessing.{schedule,collect}EventProcessing`.
    A risk for 7f-5b: the per-event goroutines call `wg.Add(1)` while `run` may be in
    `resultChanWG.Wait()`. This is legal only because the scheduler's own count is held, and the
    thread-token-backed `WaitGroup` spec must allow an `Add` during a `Wait` at a positive count.
  - The protocol: `incomingEventChan` is an SPSC queue (the producer is `startWatching`, the
    consumer is processing) whose elements carry the ideal stream's next item. `resultChan` has
    two producers (`sendEvent` in order; `sendError`, which carries nothing).

### 5.4 The driver

- **New functions, each with its spec:**
  - `genWatch`/`genWatchFrom`: any watch input with `inOk`;
  - `watchOptions`, `toWEvent`, `lastObj`, `watchEvents`;
  - `encodeWEvents`/`decodeWEvents` (the Lean side as `encItemsL`: `decodeWEventsL (encodeWEventsL
    evs) = some evs`, from the codec's round trip, and injectivity);
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
- **The codec's contract** gains decoding without a target, and `Obj`'s metav1 accessors the
  annotation. Both are 7e's now (`90b6252aa5`).

## 6. New trusted text and premises, with their producers

| Item | Kind | Producer |
| --- | --- | --- |
| `watchOk` and its helpers, `encodeWEvents`/`decodeWEvents`, `changeAt` (the Go copy of `WatchValidator`, specialized; the departures of §4.2 with the user's two conditions) | trusted checker text (D30m, as `Model`) | this stage; 7g's maintainers' `WatchValidator` is a refinement except at departures 1-2 (§9) |
| `featureOn g "WatchList"` from `Set("WatchList=true")` | gate fact | sweep repairs 1's B5 interface, extended with the `true` half (one joint restatement, as for 7e's `featureOff`); `axiom` skill before use |
| `ConcurrentWatchObjectDecode` | **none**: `processEvents` is proved for both values of `Enabled` (Q7f-3) | - |
| `clientv3.WithRequireLeader` over a `watchCtx` parent: a `watchCtx` with the parent's `Done`/`Err` and outgoing metadata the parent's plus `hasleader: ["true"]` | new trust-boundary triple (names-only, grpc `metadata`); generalizes the `Background()` one | 7f-3/7f-5a Draft; `axiom` skill |
| `metadata.incomingOf ci' = metadata.incomingOf ci` for the require-leader wrapper's context | reviewed trust-boundary fact (grpc metadata; `incomingOf` is opaque) | 7f-4 Draft; `axiom` skill |
| `srvCtxWeak` (the handler's weak context) and the changed `srvStreamInterceptorOk` | changed grpc model contract (InvGrpcStream), proved for etcd's interceptors and grpc-prometheus's | 7f-4 |
| P-RL1 (restated, §3), only if the Draft needs it | Perennial spec, general, proved in Perennial | independent Perennial change |
| P-RL2: context derivations (`WithValue`, `WithCancel`/`WithTimeout`) over a weak parent | Perennial spec, general (or local lemmas until it lands) | 7f-4 Draft; independent Perennial change |
| `runtime.Decode` | translation (`runtime.toml` gains it), no trust | 7f-5a |
| `store.getResourceSizeEstimator` / `collectorMux` | a reader slot (bounds files) and a store invariant (estimator nil), no trust | 7f-5a; `etc/bounds-*.txt` |
| `errors.As` (two error types), `fmt.Errorf` (`%q`, `%d`, `%s`), `Event_EventType.String` | Perennial's specs; `String` translated or a local spec | 7f-5a Draft |
| `apierrors.NewInternalError`, `NewResourceExpired`, `APIStatus.Status` | translations, or local specs | 7f-5a Draft |
| `wait.Jitter` | local trust-boundary spec ("some duration") or translation | 7f-5a Draft; `axiom` skill |
| `clientv3.Event.IsCreate`, `WithPrevKV`, `utilflowcontrol.WatchInitialized` (with `initializationSignalFrom`) | translations (configuration), no trust | 7f-3/7f-5a |
| `klog.V` and `klog.Errorf` (specs exist); `Verbose.Enabled`, `Verbose.InfoS`, `klog.Warningf`, `metrics.RecordEtcdEvent`/`RecordEtcdBookmark` (`RecordEtcdRequest`'s exists); `clock.RealClock.Now` (exists) | no-op specs in the existing pattern, each listed in 7f-5a's Draft | 7f-5a |
| `v3rpc.runsNoRequireLeader` | **removed** premise (deployment; the user's decision) | deleted once 7f-4 proves the branch |
| watcher bounds: `watchers·wops` and the goroutines per watch under adequacy's thread bound | adequacy constants | the grpc serve pool's stage B (thread-token pool) |

No etcd fork change (the user's decision).

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
- the grpc stream model's users of `srvStreamInterceptorOk`/`grpcStreamHandlerOk`
  (`InvGrpcStream`), and every registered stream handler over the weak context: the v3rpc watch
  proofs (`watchServer__Watch`, `serverWatchStream__{recvLoop,sendLoop,isWatchPermitted}`) and
  the lease keep-alive (`LeaseServer__LeaseKeepAlive`, `LeaseServer__leaseKeepAlive`);
- the stream interceptor's (`newStreamInterceptor`, `monitorLeader`);
- lintest's `Run`/`RunLin` callers: none re-proved, since their specs are kept.

**Interface files:**
- raft's API is untouched;
- `etcdstart`'s interface files change if `commonPremises` does
  (`interface/Proof/.../lib/etcdstart/*.txt`).
- Each Draft shows the diff.

**Vacuity**, as for 7e: until the per-type landing (`pbEnc_ok`), sweep repairs 1 and the grpc serve
pool's fix, these theorems are vacuous or rest on false axioms. 7f's value arrives with them.

## 8. The Go prototype

`notes/k8s-7f-proto.patch` applies to `k8s-7e` `7f2ad6c9b5` (checked with `patch --dry-run` on a
fresh archive). It touches seven files:

| File | Contents |
| --- | --- |
| `examples/lib/lintest/lintest.go` | `RunLin2`; `RunLin` now calls it |
| `examples/k8s/etcd3/k8setcd3.go` | the watch fields of `Input` and `Output` (`WEvents` a string), the step's `KWatch` branch, `Gen`/`Apply`, `Check` with `watchers, wops` (through `RunLin2`), `Main`/`MainCluster`/`MainPartition` with `watchers, wops` and `WatchList` on |
| `examples/k8s/etcd3/watch.go` | `genWatch`/`genWatchFrom`, `runWatch`/`watchEvents`, `toWEvent` (with `WBad`), `encodeWEvents`/`decodeWEvents`, `changeAt` (a merge), `watchOk` and its helpers |
| `examples/k8s/etcd3/watchmain.go` | `watchList()`, and the tests' helpers (`checkWWith`, `newStoreW`, `clusterW`) |
| `examples/k8s/etcd3/k8setcd3_test.go` | the existing tests call `Main*` with 0 watchers |
| `examples/k8s/etcd3/watch_test.go` | the tests below |
| `examples/k8s/etcd3/errorder_test.go` | §2.4 |

**The Goose dry run.** `etc/goose.py --project k8s-apiserver --project lintest` was run with the
pinned Perennial (`84d538063`), in a throwaway worktree at `7f2ad6c9b5` plus the prototype, then
removed. It succeeded. Every new function translates with its body, including `genWatchFrom`,
`watchEvents` (the `select`s on timers), `runWatch`, `encodeWEvents`/`decodeWEvents`, `changeAt`,
`watchOk`, `reliableOk`, `initialPrefixOk`, `bookmarksOk`, `toWEvent` and `RunLin2`. That adds
3876 lines to `Code`/`GeneratedProof`. Elaboration was not checked.

**Runs**, each test in its own process, all under `systemd-run -p MemoryMax=32G`, `GOWORK=off`:

| Test | Configuration | Result |
| --- | --- | --- |
| `TestWatchOkEdges` | `watchOk` on hand-made histories | a bookmark at `c.st.rv + 1`, a bad event and a dropped middle event are rejected; a full window, a bookmark at `c.st.rv` and an Error between events are accepted; a dropped first event of an unpinned watch is accepted (the documented blind spot); the encoding round-trips |
| `TestMainWatch` | one member; 8 unary clients × 300, 16 watchers × 8 | `Ok`, 2 of 2 runs, 9-13 s (the pacing makes watches longer), peak RSS 137-144 MB. 52-53 watches (all four behaviours), 27-33 with events, 8-14 watch-lists with events. Per run: 500-600 Added, 260-440 Modified, 500-580 Deleted, 8-14 initial-events bookmarks, no bad event. Revisions up to 535. |
| `TestWatchCorrupt` | one member; 4 × 60, 8 × 6 (small: porcupine searches exhaustively before it answers Illegal; at 8 × 300 one `dup` run took more than 3 minutes); the first watch with change events corrupted, retried on a fresh member when none had any | **12 of 12 rounds**: `Illegal` for each of `value`, `rv`, `type`, `dup` and `drop` (now a middle event of a watch with at least 3), and `Ok` for `none`; 0.7-3 s each |
| `TestMainPartitionWatch` | three members; 4 × 60, 8 × 12; schedules `isolate`, `election`, `blackhole`, `drop`, `mixed` (7c's) and `noleader` (every peer link cut for 6 s) | **`Ok` in 30 of 30 runs** (5 rounds × 6 schedules); peak RSS 74-180 MB, one `blackhole` run 497 MB; 0.5-16 s each. The runs reach failed unary calls (0-4 per run), failed `Watch` calls (up to 9 per run) and Error events (3 runs; 7 watches in one); no bad event. |
| `TestErrorEventNotLast` | a fake client watcher | an Error before later events in 7 of 50 trials on the rebased tree (1-12 over all runs, §2.4) |

The whole package passes (`go test .`, 177 s, under the cap), and so does lintest's.

**Not tested:**
- `ConcurrentWatchObjectDecode` off (the default, on, was used). 7f-0 adds a run with it off.
- No `noleader` run delivered an Error after an initial event. §2.4's test covers that ordering.

## 9. Stages, estimates, dependencies

| Stage | Contents | Lean lines | Depends on |
| --- | --- | --- | --- |
| 7f-0 | Go: the prototype made the driver (the watch fields of `Input`/`Output`, `KWatch`'s step, `Gen`/`Apply`/`Check`, `Main*` with `watchers, wops`), `RunLin` through `RunLin2`, the `WatchList` gate, mode-count tests as 7e's `TestTrafficReachesCases`, 5×6 partition runs, the Goose run | Go only (~900 lines) | 7e-0; **timed against 7e's Lean**: the new `Input`/`Output` fields change 7e's model records (`MDefs`, `encIn`, `inputEqual`, `outEqual`), so 7f-0's driver change lands either before 7e-3b(b) finishes (and 7e rebases, +200-400 Lean lines of churn in 7e) or after 7e-4 (Q7f-6) |
| 7f-1 | `lintest.RunLin2` spec and proof; `RunLin`/`Run` re-derived (`RunLin` calls `RunLin2`) | 200-400 | none (lintest only) |
| 7f-2 | pure: `WEvent`, `encodeWEventsL`/`decodeWEventsL` (round trip, from `encItemsL`'s), `watchOkL`, `changeAtL` and its one-key lemma over the reachable histories, `toEventL`, `initialEventsL`, `stepL`'s `KWatch`, and the crux `watchOkL_of_stream` (§5.4) | 1400-2300 | 7e-3a/3b (the `hist` model, `encItemsL`) |
| 7f-3 | `WithPrevKV` through the watch stack: the client spec (`isRangeWatch`, `watchStateRespOk`) and its users; **the re-proof of `watchGRPCStream.run` (3368 lines) and `serveSubstream`, the slowest proofs in the repository** (a separate line: 800-1500 of the range); the server's `recvLoop`/`sendLoop`/`swsMu`; `WithPrevKV`'s translation; the `WithRequireLeader` triple over a `watchCtx` (axiom skill) | 2000-3500 | per-type landing (InvProto/InvGrpc rewrite) |
| 7f-4 | require-leader streams, no fork change: the weak context `srvCtxWeak` and its lemmas (300-500); the changed `srvStreamInterceptorOk` and the `incomingOf` fact (axiom skill) (300-500); the interceptor branch, `cancellableContext`, `serverStreamWithCtx`, `monitorLeader` over a non-empty interface-keyed map (900-1400); Watch's handler chain re-proved over the weak context (`watchServer__Watch`, `recvLoop`, `sendLoop`, `isWatchPermitted`: about 3400 lines today, 700-1300 changed); LeaseKeepAlive's (`LeaseKeepAlive`, `leaseKeepAlive`, about 440 lines, and `LeaseRenew`'s derived `WithTimeout`: 300-600); P-RL2 (and P-RL1 if needed) as local lemmas, or in Perennial (300-600); `runsNoRequireLeader` deleted from 26 files and every closed theorem (200-400) | 3000-5300 (was 1500-2500) | per-type landing; grpc serve pool stage B (streams count against the handler pool) |
| 7f-5a | the etcd3 watcher, serial branch of `processEvents` (the concurrent one out of scope): the configuration (G1 exclusions dropped, `IsCreate`, `WatchInitialized`, `runtime.Decode`), `store.Watch.spec` and `k8sWatch`, `watcher.Watch`, `run`, `startWatching`, `sync`/`syncPaginated`, `serialProcessEvents`, `transform`..., `getResourceSizeEstimator`'s reader slot, the error paths (`errors.As`, `fmt.Errorf`), the trust specs (Draft) | 3200-4800 | 7f-3, 7f-4; 7c-3 and 7e-1 (the paginated `Get`); 7e's object layer and codec contract (decode without a target, `Obj.Annotated`); sweep repairs B5 (`featureOn`) |
| 7f-5b | the concurrent branch (scheduler, collector, per-event goroutines; the ordered queue of response channels); risk: `WaitGroup.Add` during `Wait` (§5.3) | 1000-1600 | 7f-5a |
| 7f-6 | the driver: `genWatch`, `runWatch`, `watchEvents`, `Apply`/`Gen`/`Check`, `Main*`, adequacy, the three closed theorems | 2000-3000 | 7f-1, 7f-2, 7f-5a/5b; **7e-4** (kInv's `hist[R] = absK (stateAt L R)`, which `watchOkL_of_stream` needs); stage B (adequacy's thread bound) |
| total | | 12800-20900 (was 10200-16100) | |

**The order.**
- 7f-1 and 7f-2 start once 81 approves this revision. 7f-1 touches lintest only. 7f-2 is pure,
  on 7e's `hist` model.
- 7f-0's driver change is timed against 7e's Lean (Q7f-6). Its Go tests can run on a branch
  meanwhile.
- 7f-3 and 7f-4 come after the per-type landing. They are etcd-side and benefit every watch
  example and the lease keep-alive.
- 7f-5a after them, with 7c-3 and 7e-1 in. Then 7f-6 on 7f-5a's spec and 7e-4, and 7f-5b (which
  changes no statement) before 7f-6's Freeze, since the final theorems cover both values of
  `ConcurrentWatchObjectDecode`.

**Checkpoints** (each a report to 81):
1. 7f-0's Go report.
2. 7f-2 built.
3. 7f-3's statements (the client spec's change, the `WithRequireLeader` triple).
4. 7f-4's Draft (a hard stop): the weak context, the interceptor contract, the `incomingOf` fact,
   P-RL1/P-RL2, the premise deletion.
5. 7f-5a's Draft (a hard stop): `store.Watch.spec`, `k8sWatch`, the trust specs.
6. 7f-6's Freeze package.

**7g** then translates the maintainers' `WatchValidator` (with `Replay`). As in 7e §10, its check
on runs with no failed write is a refinement of ours, except at §4.2's departures 1-2, where it is
stricter, so it could fail on the runs §2.4 describes. 7g must keep our check where they differ,
or wait for an upstream fix of the watcher.

## 10. Decisions, and the one question left

Decided (recorded in this worktree's `questions.md`):
- **Departures 1-4** (§4.2): accepted by the user (2026-11-08), on two conditions:
  bookmarks bounded by `c.st.rv`, and foreign-object events rejected (`WBad`). Both are in the
  prototype.
- **`runsNoRequireLeader`**: deleted, with no etcd fork change (the user, 2026-11-08).
- **Q7f-1** (81): (a), the existing entry points gain `watchers, wops`.
- **Q7f-2** (81): the weak handler context, the changed stream-interceptor contract with the
  reviewed `incomingOf` fact, and Watch and LeaseKeepAlive re-proved over it.
- **P-RL1** (81): restated (§3), decided in the 7f-4 Draft.
- **Q7f-3** (81): both values of `ConcurrentWatchObjectDecode`, serial first.
- **Q7f-5** (81): yes, after the non-issue's fixes (upstream now searched, the rate 1-12 of 50, one
  commit cited).

Left for 81:
- **Q7f-6. When 7f-0's driver change lands relative to 7e.** (a) Before 7e-3b(b) finishes: the
  watch fields go in now, and 7e's records are rewritten once (7e absorbs 200-400 lines). (b)
  After 7e-4 lands: 7e is untouched, and 7f-6 redoes the records. **Recommended: (a)**. The
  records are being rewritten in 7e-3b(b) right now (`7f2ad6c9b5`), and the watch fields are
  plain (`WKey`, `SendInit`, `Bookmarks`, `Behavior`, `Skip`, `WEvents` as a string, `WFailed`), so
  adding them during that rewrite is the cheapest point. 7e's owner decides the exact moment.
