# Requirements on `go.etcd.io/etcd/client/v3` (the client's other parts: 1b watch, 1c lease, lifecycle, auth, cluster, maintenance, interceptors)

## from W0

W0 owns the client's vocabulary (`Spec/go_etcd_io/etcd/client/v3/Api.lean`) and its KV path. It
left **slots** (opaque predicates whose meaning is stated in `Api.lean`'s header) for 1b and 1c to
spec against and realize, and its sketches need these of them:

1. **`clientv3.New(cfg)`** (1c): for a configuration whose endpoints are served by members of the
   cluster `γ` (`servesAt γ ep` for each, `api/v3/State.lean`) and whose credentials name the
   principal `who` (`cfg.Username`, or none; a client certificate's common name), returns
   `clientMut c γ who` (the six interface fields writable: Kubernetes' storage factory wraps
   `c.KV`) or an error; `clientMut_freeze` makes it `isClient`. Its `KV` field is
   `NewKV(c)`'s (`kvHandle_kvAt`); the other fields meet `watcherAt` (1b), `leaseAt`, `authAt`,
   `clusterAt`, `maintAt` (1c), which those batches define as bundles of their methods' triples, in
   the KV contract's shape (the caller's update over `etcdState γ`, `Model.lean`'s `Step` for their
   requests, `□` for a read, the answer's reply or `indefCall`). Prove the laws `isClient_conn`,
   `isClient_KV`, `isClient_fields`, `clientMut_KV`, `clientMut_conn`, `clientMut_freeze`,
   `handles_persistent`.
   ```go
   cli, err := clientv3.New(clientv3.Config{Endpoints: []string{ep}, Logger: lg})
   cli.KV = etcd3.NewETCDLatencyTracker(cli.KV)   // Kubernetes: a wrapper meeting kvAt
   ```
   Used by: every `Client.*.spec` (`isClient`), `NewKV.spec` (`clientConnOk`, available during
   `newClient` before `c.KV` is set).

2. **`connOk conn γ who`** and **`clientConnOk c γ who`** (1c): `Client.dial` with the retry and
   version interceptors (`unaryClientInterceptor`, `streamClientInterceptor`, `withVersion`) over
   grpc's connection to endpoints of `γ`. The **retry interceptor's discipline** is what the KV
   contract's update shapes rest on (W0's `req/` to 2a, item 3): a non-repeatable call is resent
   only after an attempt that was never sent (`isSafeRetryMutableRPC.spec`: `.notSent`), after a
   learner's refusal before the handler (`ErrGRPCNotSupportedForLearner`, with several endpoints:
   `isSafeRetry`), or after a refusal that fired nothing (a stale or invalid token: the interceptor
   refreshes it and resends). When it gives up it returns the last attempt's refusal, or the
   refresh's own error (`gtErr`: `ErrAuthFailed` for a changed password or a deleted user, a
   refusal, `EtcdErr.refusal`; any other `Authenticate` error is `.other`, indefinite), and fires the
   caller's update with that refusal itself. The **stream interceptor** calls `getToken` at every
   stream open and returns its error as the open's: a refusal that fired nothing (W0's
   `RemoteKV.RangeStreamTriple`, `KV.GetStreamTriple`, and 1b's watch streams); a repeatable call (a read, `withRepeatablePolicy`) is resent after
   `Unavailable`. With the fork's fix `8a24be2a3` a non-repeatable call returns its attempt's
   `Canceled`/`DeadlineExceeded` (`nonissues/etcd-client-retry-put-ctx-error.md`).
   Used by: `retryKVClient.*.spec`, `RetryKVClient.spec`.

3. **`callOptsOk sl rep`** (1c): the client's `callOpts` (`callOptsOk c.callOpts false`), the nil
   slice (`callOptsOk slice.nil false`: `NewKVFromKVClient` with a nil client), and appending
   `withRepeatablePolicy()` (whose spec 1c gives) to any such slice (`callOptsOk _ true`, whatever
   the capacity).
   ```go
   return rkv.kc.Range(ctx, in, append(opts, withRepeatablePolicy())...)
   ```
   Used by: `retryKVClient.Range.spec`, `NewKVFromKVClient.spec`.

4. **The principal**: `who` is what the server's auth applier sees for every request of the client
   sent with a context satisfying `ctxPrin ctx who` (its token's user, or none); a token refresh
   keeps it. `Client.Ctx()` (used by `concurrency`: `mutex.go`, `stm.go`) must give a context with
   `Context.ctxOk` and `ctxPrin _ who` (1c's spec).
   Used by: every `KV.*Triple` (`Step who rq ...`).

5. **1b (watch)**: `OpWatch.spec` (W0's) builds the watch's `Op` (`opWatchM`, `watchPanics`);
   `watcherAt v γ who` is 1b's bundle; its events are the model's history (`KVHist.eventsAt`, the
   whole history kept, `compacted` the floor) and its compaction errors the model's
   (`EtcdErr.compacted`). `WithRequireLeader.spec` gives `ctxRequireLeader ctx'` (the server closes
   a watch whose member loses its leader). W0's KV specs say nothing of watches: no snippet of
   W0 relies on one.

6. **`ContextError`** is W0's (`ContextError.spec`, over `callErr`): 1b and 1c call it after their
   own gRPC calls, as `kv.go` does.

## from 1f

The recipes (`client/v3/experimental/recipes`, `Spec/.../experimental/recipes/Api.lean`, namespace
`Recipes`) wait on watches. Until 1b's vocabulary exists they state their watch needs as **slots**
in their own `Api.lean` (`watchChanAt`, `watchEvOwn`, the laws `watchChanAt_recv`,
`watchEvOwn_unfold`); 1b's predicates replace them at integration (rename, same content).

1. **`Watcher.Watch`** (1b; a bundle triple of `watcherAt`, which `isClient_fields` gives): with any
   context (`Context.ctxOk`; the recipes pass `context.WithCancel(context.Background())`, canceled
   by a `defer` when the wait returns), a key, and the options `WithRev(rev)` (`rev > 0`) or
   `WithPrefix(), WithRev(rev)`, returns a non-`nil` `WatchChan` with **the consumer of the watch
   of the range `rg` from revision `rev`**, nothing received yet (`watchChanAt wc γ rg rev []`;
   `rg` the range `OpWatch(key, opts...)` names). If the spec needs a `threadTok` (the watcher's
   goroutines), say so: the recipes' specs would then take one.
   ```go
   ctx, cancel := context.WithCancel(context.Background())
   defer cancel()
   wc := c.Watcher.Watch(ctx, prefix, clientv3.WithPrefix(), clientv3.WithRev(rev))
   ```
   Used by: `WaitEvents.spec`, `WaitPrefixEvents.spec` (so `Barrier.Wait`, `DoubleBarrier.Enter`,
   `Leave`, `Queue.Dequeue`, `PriorityQueue.Dequeue`, `RWMutex.Lock`, `RLock`).

2. **A receive** (`for wresp := range wc`): the channel closed (at any time); or a response whose
   `Err()` is not `nil`; or a response with `Err() = nil` whose `Events` (read-only `*mvccpb.Event`s)
   extend what was received **within the cluster's history of `rg` from `rev`**: with `etcdLb γ σ`,
   everything received so far is a prefix of `watchHist σ.kv rg rev` (every event of the range at
   revisions `≥ rev`, in revision order, none skipped, a revision's events in their order; the
   history is W0's whole `KVHist`, so a compacted start revision is an error response, not a gap).
   The recipes' slot law `watchChanAt_recv.spec` states it over `chan.receive` and the response's
   fields (`closeErr`, `CompactRevision`, `Canceled` decide `Err()`).
   ```go
   for wresp := range wc {
       if err := wresp.Err(); err != nil { return nil, err }
       for _, ev := range wresp.Events { if ev.Type == evs[i] { ... } }
   }
   ```
   Used by: `waitEvents.spec` (the first delete or put after a revision: the barrier released,
   the queue's first put, a lock key gone).

3. **`WatchResponse.Err`** (1b): `nil` iff `closeErr` is `nil`, `CompactRevision` is `0` and
   `Canceled` is false (`watch.go`'s switch); and the error it returns is never one of the recipes'
   `errors.New` sentinels (`recipeErr e`): it is `errVal` of an rpctypes error or a gRPC status
   error. The recipes' `DoubleBarrier.Enter.spec` distinguishes `ErrTooManyClients` from every
   other error.

4. **An event's fields** (1b or 3h: whoever owns `mvccpb.Event`'s predicate): for a delivered
   event `e`, `Type` is `PUT` (0) for a put and `DELETE` (1) for a delete, and `Kv` points to a
   read-only `KeyValue` with the key, and for a put the new record, for a delete the event's
   revision as `ModRevision` (`WatchEv.kvM`; the recipes' slot `watchEvOwn_unfold`).
   ```go
   ok, err := deleteRevKey(q.client.KV, string(ev.Kv.Key), ev.Kv.ModRevision)
   return string(ev.Kv.Value), err
   ```
   Used by: `Queue.Dequeue.spec`, `PriorityQueue.Dequeue.spec`.

5. **(W0) A shared permission to observe.** The recipes take `etcdPeek γ` (a persistent atomic
   update leaving `etcdState` unchanged) for their `Get`s; 1d's `Concurrency.etcdPerm γ readEff`
   is the same thing (its commit also gives `etcdLb` of the states). Suggestion: W0 owns one
   `etcdPerm γ T` in `api/v3/State.lean` (1d's definition), and the recipes' `etcdPeek γ` and
   `dbPerm` become `etcdPerm γ readEff` and `etcdPerm γ (dbEff ...)`.

## from 1b

1b fills W0's slot `watcherAt v γ who` (`watcherAt_methods.spec`: the `Watcher` interface's
`Watch`, `RequestProgress`, `Close` triples, `ApiWatch.lean`) and realizes it for `*watcher`
(`watcherHandle_watcherAt.spec`, `NewWatcher.spec`). What its sketches need of 1c:

1. **`Client.GetLogger()` under `clientConnOk c γ who`** returns a logger with `Zap.isLogger` (not
   `nil`: `run` logs failed sends with `w.lg.Debug`, which dereferences the logger), during
   `newClient` (before `isClient`). Used by: `NewWatchFromWatchClient.spec`.
2. **`isHaltErr(ctx, err)`, `isUnavailableErr(ctx, err)`** (`client.go`): for a `ctxOk` context and
   an error with a `callErr` kind, a `bool`, no panic (their values are not used by 1b's
   statements). Used by: `run`, `openWatchClient`, `backoffIfUnavailable`.
3. **`newBlockLogger`, `blockLogger.recordWait`** (`block_logger.go`): no panic, the callback run
   by the goroutine that owns the substream. Used by: `newWatcherStreamBufLogger.spec`,
   `recordBufWait.spec`.
4. **Every stream of the client is its principal's**: W0's item 4 for streams: a watch stream
   opened with any context (whatever metadata the caller put in it) is authenticated as `who` (the
   token comes from the per-RPC credentials, not from the context), so the member's permission
   check of a create is `who`'s. With it, the stream-key collision
   (`nonissues/etcd-watch-stream-key-collision.md`) changes nothing in 1b's statements.
   Used by: `watchStep`'s event case (`σa.permits who`), `ReqWatchRefused`.
5. **`Client.Close`** calls `c.Watcher.Close()` (`watcherAt`'s `CloseTriple`: any number of
   times, concurrently) and drops its error.
   (Update, after W0's round 1: item 4 is W0's `ctxPrin ctx who`, which `Watcher.WatchTriple`,
   `RequestProgressTriple` and `remoteWatchAt_watch` now take; `valCtx_ctxOk` passes it to the
   stream's context, `ctxPrin_child` to its `WithCancel` child.)

## from 1e

1. **(W0) A client whose `KV` field holds a leasing KV** (the proxy: `client.KV, _, _ =
   leasing.NewKV(client, pfx)`, `server/etcdmain/grpc_proxy.go:488`, then `grpcproxy.NewKvProxy(client)`):
   `clientMut_KV`/`clientMut_freeze` require `kvAt` of the new value, which the leasing KV does not
   meet (it meets 1e's weaker `Leasing.lkvAt`, and W0's `KV.CompactTriple`/`GetStreamTriple`).
   Needed: a way to freeze a client whose KV field meets another contract (e.g. `isClient` with the
   KV field's bundle as a parameter, or `clientMutRest` persistent enough for the other fields).
   Also, `NewKV` takes `isClient cl γ who`; the proxy calls it while the KV field is still writable
   (`clientMut`): `NewKV` reads `cl.KV` once, synchronously, and the session monitor later reads
   `cl.Lease`/`cl.Ctx()` (not `KV`), so a persistent "everything but the KV field" fact suffices.
   Used by: `NewKV.spec`, snippet `leasing/lifecycle.go` (`ReqNewKVProxy`).
2. **(1c) `cl.Ctx()`**: a context with `Context.ctxOk` and `ctxPrin _ who` (the leasing KV's own
   context is `WithCancel` of it: `ctxPrin_child`). Used by: `NewKV.spec`.
3. **(1c) the lessor's `Grant`/`KeepAlive`** (under 1d's `NewSession`): their updates buildable from
   a persistent update over `leaseGrant`/`leaseKeepAlive` steps (1e's `protoUpd`). Used by
   `leasingKV.monitorSession.spec`.
4. **(1b) `cl.Watcher.Watch(ctx, key, WithRev(rev+1))`** from a `watcherAt` value: no panic, a
   channel closed once `ctx` is done; each response's `Events` a slice of events whose `Kv` is
   non-nil with readable `Value`, `Lease`, `ModRevision`, and `Type` readable. Nothing about which
   events (the leasing contract claims nothing the protocol's watches decide).
   ```go
   for resp := range lkv.cl.Watcher.Watch(cctx, lkv.pfx+key, v3.WithRev(rev+1)) {
     for _, ev := range resp.Events { if string(ev.Kv.Value) != "REVOKE" { continue } ... }
   }
   ```
   Used by: `leasingKV.monitorLease.spec`, `leasingKV.waitRescind.spec`.

## from 1d

Batch 1d (`Spec/go_etcd_io/etcd/client/v3/concurrency/`) calls the client's KV contract (W0), the
`Lease` field (1c, `ApiLease.lean`'s `Lease.methods`) and the `Watcher` field (1b, `ApiWatch.lean`).
Every update it hands those calls is built from the caller's `Concurrency.etcdPerm γ T` (a
persistent update performing any transition `T σ σ'`): the shapes W0's `KV.*Triple` and 1c's
`CallTriple` already have suffice.

1. **(1c) `Client.Ctx()` and `Client.GetLogger()` under `isClient c γ who`**: the client's context
   with `Context.ctxOk` **and `ctxPrin ctx who`** (it is `newClient`'s `WithCancel` child of the
   configuration's context: no other principal's metadata), and a logger with `Zap.isLogger`.
   ```go
   ops := &sessionOptions{ttl: defaultSessionTTL, ctx: client.Ctx()}   // NewSession
   m.Unlock(client.Ctx())                                              // Mutex.Lock's cleanup
   ```
   Used by: `NewSession.spec` (`optCtxOk` when no `WithContext`), `NewSTM.spec`,
   `Mutex.Lock.spec`, `lockerMutex.Lock/Unlock.spec`, `Election.Campaign.spec`.
2. **(1c) `KeepAlive` takes no thread token** and returns a non-nil channel (`Lease.methods` as
   written: kept). `NewSession` is called in loops (leasing's monitor, v3election's per-RPC
   sessions): a per-call token the lessor keeps would exhaust the bound.
   Used by: `NewSession.spec` (its premise has one `threadTok`, for its own goroutine).
3. **(1b) Header revisions non-decreasing along one watch channel**: `watchStep` gives each
   header `≤` a reached revision and `≥` its last event's; `Election.observe` also forwards each
   response's header to its observers and promises them non-decreasing headers
   (`observeAt_recv`). Wanted: a response's header revision is at least the previous response's
   (etcd's watch stream sends in revision order). If 1b prefers not to, 1d drops the order from
   `observeAt_recv` (and `ReqObserve`'s check).
   ```go
   case ch <- &v3.GetResponse{Header: wr.Header, Kvs: []*mvccpb.KeyValue{ev.Kv}}:
   ```
   Used by: `Election.observe.spec`, `observeAt_recv.spec`.
4. **(1b) A put event's `Kv` is non-nil and readable; a response with events owns its header**
   (`WatchRespM.hdrDq`, as written: kept). `observe` writes `hdr.Revision = kv.ModRevision` on the
   first put after an empty prefix, then hands the header (and `ev.Kv`) to its observers read-only.
   Used by: `Election.observe.spec`.
5. **(W0 / 2a) A client call's error is never one of `concurrency`'s error values**
   (`ErrLocked`, `ErrSessionExpired`, ...: `errors.New` values of that package's initialization).
   True of the code (gRPC statuses, `rpctypes` errors, context errors, other packages' values); not
   a law today, so a caller of `TryLock` that tests `err == ErrLocked` cannot exclude that a
   transport error is that value. A law over `callErr` (e.g. `callErr err k ⊢ ⌜err ≠ v⌝` for every
   value `v` held by a global of a package the client does not import) would close it; until
   then `ReqTryLock` assumes it. Open question in `notes/specs-only/batch-1d.md`.
   Used by: `ReqTryLock`, and any caller distinguishing `ErrSessionExpired`, `ErrElectionNoLeader`,
   `ErrElectionNotLeader` from a transport error.

## from 1g

The cache (`cache/cache.go`) holds the client's `KV` and `Watcher` fields (`isClient_KV`,
`isClient_fields`) and uses them from its own goroutines. What its sketches need:

1. **The watch (1b's `Watcher.WatchTriple`, `watchChAt_recv`, `watchStep`)**, as `watchEvents` uses it:
   ```go
   watchCh := c.watcher.Watch(c.internalCtx, c.prefix, clientv3.WithPrefix(), clientv3.WithRev(rev),
       clientv3.WithProgressNotify(), clientv3.WithCreatedNotify())
   for resp := range watchCh { readyOnce.Do(c.ready.Set); if err := resp.Err(); err != nil { ... }; c.demux.Broadcast(resp) }
   ```
   Each response's `watchStep` facts at the watch's position: events exactly the range's events of
   whole revisions from just after the position to the last event's (1b's `lo..c'` with
   `c' =` the last event's revision), a progress notification quiet and **not below the position**
   (1b's `c ≤ P`: the cache's demux takes it as its newest revision;
   `issues/cache-stale-progress-compacts-newest-watch.md` is the case where it is not, which the
   cache's specs now tolerate as a spurious compaction cancel, not a wrong delivery), errors
   (`Err() != nil`) settle nothing the cache states. Covered by 1b's `ApiWatch.lean` as written.
   Used by: `Cache.watchEvents.spec`, `demux.Broadcast.spec` (`respFact`), hence `Cache.Get.spec`,
   `Cache.Watch.spec`.
2. **Shared events**: the cache hands one upstream response's `*mvccpb.Event`s to every one of its
   watchers and to its store (and returns their `Kv`s from `Get`), so it needs to make a received
   response's events read-only: a law `eventOwn p (DFrac.own 1) e ⊢ |==> eventOwn p DFrac.discard e`
   (with `keyValueOwn`'s, the same for a `KeyValue`; W0's `replyPersist` covers only replies), and
   `watchRespAt v m ⊢ |==>` its read-only form. Used by: `Cache.watchEvents.spec`,
   `store.Restore.spec` (the list's key-values kept by the store: `replyPersist` suffices there).
3. **`WatchResponse.IsProgressNotify()`** (a value receiver through a pointer, `watch.go:139`): its
   spec over `watchRespAt` (`m.isProgressNotify`), nil-safe on the header. Used by: the cache's
   users (`examples/specreq/cache/watch.go` `ReqProgressQuiet`, `cachekv.go`'s `awaitProgress`) and
   `demux.updateStoreLocked`/`validateRevisions`/`store.Apply`.
4. **`RequestProgress`** (1b's `Watcher.RequestProgressTriple`): any error, no panic; the cache's
   progress requestor calls it from its own goroutine with the cache's context
   (`progressNotifierOk`). Covered as written.
5. **One vocabulary for the cache's watch channel?** The cache's `Watch` returns a
   `clientv3.WatchChan` too, but its specs use the cache's own consumer predicate (`Cache.cacheWatchAt`,
   its own `Cache.WatchRespM`/`eventOwn`, written before 1b's landed). Whether the cache's channel
   should meet 1b's `watchChAt`/`watchStep` (making the cache a drop-in `Watcher`) is an
   integration question (batch-1g.md); no change asked of 1b now.

## from 1c (to W0)

Batch 1c realizes several of W0's client slots; what it needs W0 to change or confirm (each also
an open question in `notes/specs-only/batch-1c.md`):

1. **The readiness gap** (`NewKV.spec`, `kvHandle_kvAt`): `newClient` builds the members (`NewKV`,
   `NewLease`, ...) from the connection before it sets `c.Auth`; a call made through a member then
   would, on a token refusal, refresh the token through a `nil` `Auth` and panic. No call is made
   then, but W0's `clientConnOk` (persistent, given to `NewKV`) yields `connOk`, with which a call
   can be made: 1c cannot realize it so. Proposal: `clientConnOk` gives the connection and options
   but not the right to call; `kvHandle_kvAt` (and 1c's `lessorHandle_leaseAt`, ...) take a
   persistent `clientReady c` that `isClient` and `clientMut` give (minted when `newClient` sets
   `Auth`). Alternative: keep W0's statements and accept the gap as a known unprovable step.
2. **`clientMut` makes only `KV` writable** (1c's realization: the interceptor, `Close` and
   `autoSync` read the other fields concurrently): the header's "six interface fields writable"
   should say so; 1c adds `clientMut_fields` (the other five, read-only, with their bundles: 1e's
   item 1 needs it).
3. **`callOptsOk sl false` is full to capacity** (`callOptsOk_full`: every client options slice is a
   three-element literal or `nil`), so `append(opts, withRepeatablePolicy())` allocates; the
   `retryKVClient.Range` sketch's "unless the capacity allows" should go (an in-place append would
   race between calls). `callOptsOk_append` is the law the sketch uses; `withRepeatablePolicy.spec`
   gives `repOptAt`.
4. **A stream's open may fail with a definite refusal** (the stream interceptor's `getToken` error,
   `siOk_call`): `RemoteKV.RangeStreamTriple`'s open-error disjunct (`indefCall err`) should admit
   `∃ e, callErr err (.etcd e) ∗ ⌜e.refusal⌝` (for a read nothing needs firing), and `kv.GetStream`'s
   post accordingly (`ContextError` gives `errVal e`).
5. **One read permission**: 1c's `idUpd γ` (`ApiClient.lean`: the identity update the client's own
   `Authenticate` and `MemberList` need) is 1d's `etcdPerm γ readEff`, 1f's `etcdPeek`, 1g's: one
   definition in `State.lean` (as 1f, 1d and 1g asked) would replace it.
6. **The lease model** (noted, no change needed by 1c): the client specs do not use the model's
   `.leaseKeepAlive` step (a keep-alive takes no update: it changes nothing and its answer is any
   TTL); `examples/etcd/leaseexpiry` reads `GrantedTTL == 0` as "not found", which the model allows
   for a found lease too (`ttl ≤ gttl` only).

## from W0 (round 2): a client whose `KV` field another contract meets (for 1c, 1d, 1e)

W0 added `clientRest c γ who` (persistent: everything of the client but its `KV` field) with
`clientMut_split` (`clientMut` gives the `KV` field's points-to, writable, its current `kvAt` value,
and `clientRest` for good), `isClient_rest`, `clientRest_conn`, `clientRest_fields`
(`Spec/go_etcd_io/etcd/client/v3/Api.lean`). The gRPC proxy's `client.KV, _, _ =
leasing.NewKV(client, pfx)` (1e's item 1) is then: split, call `leasing.NewKV` with `clientRest` and
the `KV` field (it reads `client.KV` once), write the leasing KV into the field, and keep `c.KV ↦ lkv`
(or `↦□`) with 1e's `lkvAt`. 1c's `New` returns `clientMut` as before and realizes `clientRest`
with it; 1d and 1e cite `clientRest` where they need the client's context, lease or watcher but not
its `KV` contract. The promoted `Client.{Get,...}` specs still need `isClient` (the `kvAt` contract).

### from 1b, round 1: answers to other batches' requests

* **To 1d (item 3, non-decreasing header revisions along a channel): false of the code, not
  given.** An unsynced watcher's batch is cut at `watchBatchMaxRevs` with the header at the store's
  revision (`server/storage/mvcc/watchable_store.go:397-401`), so a response can carry header `H`
  with its last event `c' < H`; after a reconnect to a member at a revision in `(c', H)` the next
  response's header is below `H`. What is given: event revisions strictly increase across
  responses and a progress notification is never below the last event (`watchStep`); drop the
  header order from `observeAt_recv`.
* **To 1f (item 1)**: `Watch` returns a non-`nil` channel (`⌜ch ≠ null⌝` in `Watcher.WatchTriple`).
* **To 1g (item 2)**: `watchRespAt_persist` (to `watchRespRO`, persistent: header and events at
  `DFrac.discard`) and `eventOwn_persist`.

## from 2b (to 1b: a correction of `wireStep`)

Batch 2b (the member's watch handler, `v3rpc/watch.go`) states its contract as 1b's wire protocol,
`srvWireStep` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean`): `wireStep`
with **one correction**, which 2b needs 1b to adopt in `wireStep` itself (then `srvWireStep` is
`wireStep`, and 2a's boundary can carry a sent response's facts to the client's `Recv`).

**The id `-1` case is false of the member.** `wireStep` says a progress notification of id `-1` at
`P` is a progress of *every* registration of the client's state `st`. A client that cancels a watch
`W` the member has not caught up with (an unsynced watcher, events below `P` not yet sent), then
requests progress, can receive the progress at `P` before `W`'s cancel response: the member's
`recvLoop` runs mvcc's `Cancel(W)` (so `RequestProgressAll` no longer counts `W`) and queues the
cancel response on the control channel; the progress goes through mvcc's channel; `sendLoop`'s
`select` may take the progress first; `W`'s missing events are never sent. `W` is still in the
client's `st.regs` (its cancel response has not arrived), so the progress's claim about `W` is false.
(Found by code reading: `watch.go:374-402` and `:514-546`; no test written.)

**The correction**: in the id `-1` case, a registration `r` whose cancel request the member had
read (`WireWatchReq.cancel r.1 ∈ ss`) is exempt and keeps its position:

```lean
(∀ r ∈ st.regs, WireWatchReq.cancel r.1 ∉ ss →
  ∀ c, r.2.2.done = some c → c ≤ P ∧ watchEvents r.2.1 σ.kv (c + 1) P = []) ∧
st' = { st with
  regs := st.regs.map (fun r => if WireWatchReq.cancel r.1 ∈ ss then r
                                else (r.1, r.2.1, { r.2.2 with done := r.2.2.done.map (fun _ => P) })),
  frag := none }
```

**What it costs the client: nothing observable.** `run` sends a watch's cancel only after
`closeSubstream` removed it from `w.substreams` (`watch.go:695-715`), and for a response of an
unknown id (`:663`, no substream); `broadcastResponse` sends a progress only to `w.substreams`
(`:756`). So the exempt registrations are never delivered the progress; 1b's `run` sketch must use
that (a registration whose cancel was sent has no substream). Used by 2b's `sendLoop` sketch (the
progress of id `-1` covers the registrations live when mvcc produced it; one canceled before then
had its cancel request received).

Also (no change asked): 2b's sketches meet 1b's round-1 changes (`WireSt.frag` with its id; a
registration from `0` at `WatchPos.init 0 H`, `H` the `Created` header's revision: the member
registers at `R` and reads `H = Rev()` after, `R ≤ H`, its events from `R + 1`).

## from 1d (round 1)

Updates to "from 1d": item 3 (non-decreasing watch headers) is **withdrawn** (1d's `observeAt_recv`
no longer orders headers: false after a reconnect to a lagging member); item 5 is met by W0's
`callErr_errorsNew` (1d adds `concErrVal_notCanceled`). Item 1 is restated, and a new need:

1. **(1c, W0) `Client.Ctx()` gives a context of the client's own principal**: under `isClient c γ
   who` (or `clientRest c γ who`), `ctx` with `Context.ctxOk ctx ∗ ctxPrin ctx who'` for a principal
   `who'` with `isClient c γ who'` (for an ordinary client `who' = who`). 1d's cleanups run on it:
   `m.Unlock(client.Ctx())` (`mutex.go:92,99`), `e.Resign(client.Ctx())` (`election.go:98`),
   `lockerMutex`; `NewSession`/`NewSTM` without a context option.
   Used by: `Mutex.Lock.spec`, `Election.Campaign.spec`, `lockerMutex.*.spec`, `NewSession.spec`,
   `NewSTM.spec`.
2. **(W0, 2e) The in-process client's principal is per request** (the completeness review's C5):
   v3lock and v3election use `v3client.New(s)`, whose KV and Lease call the server's handlers with
   the caller's context, so each request runs as the principal of that context's incoming metadata
   (`server/auth/store.go`'s `AuthInfoFromCtx`), not as one principal fixed by the client. 1d's
   specs now take the principal per call: each mutex/election method takes `isClient c γ who` and
   `ctxPrin ctx who` for its context; the session names only its client (`isSession s c γ id`).
   Wanted from W0: for the in-process client, `isClient c γ who` for **every** `who` (or a
   `clientRest`-style handle with a per-call `who`), and `ctxPrin rpcCtx who` for the RPC context
   of a request authenticated as `who` (2e/2a: the server side establishes it). The cleanups on
   `client.Ctx()` then run as the in-process client's own principal (none, with auth on: refused,
   `nonissues/etcd-v3lock-auth-cleanup-unauthenticated.md`); 1d's specs only need their effect to be
   within the permission, which a refusal is.
   ```go
   s, err := concurrency.NewSession(ls.c, concurrency.WithLease(clientv3.LeaseID(req.Lease)),
       concurrency.WithContext(ctx))       // ctx: the Lock RPC's context
   m := concurrency.NewMutex(s, string(req.Name)); err = m.Lock(ctx)
   ```
   Used by: every 1d spec at v3lock's and v3election's call sites.

## from 1e (round 1)

5. **(W0) A per-request principal.** The gRPC proxy sends each request with its requester's token
   (`AuthUnaryClientInterceptor`, `server/etcdmain/grpc_proxy.go:345`), so with auth on its calls run
   as many principals through one client. `kvAt v γ who` and every `KV.*Triple` fix `who` (with
   `ctxPrin ctx who`); the leasing contract follows them. Needed for the proxy with auth: the
   principal taken per call (`ctxPrin ctx who'` for any `who'`), the handle not naming one. Until
   then 1e's snippets model the proxy with auth disabled. Related finding:
   `nonissues/grpcproxy-leasing-auth-cached-read.md`. Used by: every `LKV.*Triple`.

## from W0 (round 3): lease reads per member, the principal per call (for 1c; 1d, 1e, 1f, 1g follow)

1. **Lease reads** (`lessor.Leases`, `TimeToLive`): the model answers them from a lease table of the
   answering member's lessor (`State.leaseAnsAt σ i`, `State.leaseTables`); 1c's specs state, for a
   client of one endpoint `ep`, that a `Grant` through `ep` gives `leaseViewLb γ ep i` of the table
   after it, and a `Leases` through `ep` holding `leaseViewLb γ ep i` is answered at a table `≥ i`
   and gives its own (`TimeToLive` likewise for the leader's lessor). What
   `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}` need (`batch-W0.md`, Round 3).
2. **The principal is per call**: every client call takes `ctxPrin who ctx p` (`who` the client's
   own credentials, `p` the call's principal) and its update is `Step p ...`. 1c's `Authenticate`
   gives `tokenUser γ tok u` for the token it returns (from 3d's token provider); `Client.Ctx()`
   gives `ctxPrin who ctx who`; 1c's lease, auth, cluster and maintenance contracts follow the KV
   triples' shape.

## from 2a

What 2a's boundary gives 1c and W0 to realize their slots, and needs of them (`Spec/google_golang_org/
grpc/Api.lean`, `Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Api.lean`,
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Api.lean`):

1. **`connOk`** from `Grpc.connAt cc A ui si R` (`Grpc.NewClient.spec` with the client's options:
   `WithUnaryInterceptor`, `WithStreamInterceptor`, `WithResolvers` of a `resolverAt r A` with
   `A ep := servesAt γ ep`, `WithPerRPCCredentials` of a `perRPCAt pc R` with `R` "the token metadata
   names `who`", `WithTransportCredentials`); `dialOptsOk sl` realized as "each option `dialOptAt v
   id`" (neutral: keepalive, dialers, stats, block; never `WithUnaryInterceptor`, nor a default
   service config with a retry policy). `NewClient` takes the workload premise `Grpc.msgsFit`:
   `cfgOk` (or `New.spec`) must carry it.
2. **`AttemptTriple`** from `Grpc.attemptOk_call` with the method's contract `V3rpc.etcdUnary γ m`
   (`servesAt_addr` and `etcdContract`'s table): the caller builds `S md c Φ` from its `callAU`, its
   principal (`V3rpc.mdPrin γ md who`, from `ctxPrin` and the credentials' `R`: an introduction law
   1c and 3d owe, `mdPrin_of`), and `Φ` mapping the outcome: `.ok c` to success (the reply holder's
   content, 3h's relation), a status with a mapped definite description to case 2, the token or
   learner refusal to case 3 (the update back), anything else (`indefMsg`, `ownErr`) to case 4.
3. **The keep-alive stream** (`kaSendAt`, `kaRecvAt`): `Grpc.cliSend`/`cliRecv` of a stream opened
   on `/etcdserverpb.Lease/LeaseKeepAlive` with `V3rpc.kaSpec γ` (its messages carry nothing:
   `True`); `Recv`'s errors: `Grpc.ownErr` or a handler's status, classified by
   `Rpctypes.callErr_status`/`callErr_unmapped`/`callErr_ownErr`.
4. **Error classification**: `callErr` is realized by `Rpctypes.callErr_view` (what `status.FromError`
   sees of each kind) and introduced by `callErr_status`, `callErr_unmapped`, `callErr_ownErr`;
   `status.Error(code, msg)` with a message that is no mapped description is `.other`
   (`callErr_unmapped`: 1e's `Unimplemented`, 1c's `Canceled`/`DeadlineExceeded`/`Unknown`).
   `io.EOF` from a stream's `SendMsg`/`RecvMsg` is `.other`: a law for W0's `callErr` (io.EOF is no
   status, its message no description), which 2a can add when W0 states it.
5. **`tlsCfgOk`**: `V3rpc.Server.spec` takes 1c's `Transport.tlsCfgOk` for the server's TLS
   configuration (the same `credentials.NewTransportCredential`).

## from 1c (round 1, to W0)

1. **Readiness in the KV handle's introduction** (1c's `clientReady c`, `ApiClient.lean`): `newClient`
   builds `NewKV(c)` before it sets `c.Auth`; a call through the handle in that window would refresh
   a token through a `nil` `Auth`. 1c's handles now record their client and meet their bundles only
   with `clientReady c` (`authHandle_authAt`, `lessorHandle_leaseAt`, ...); the interceptor laws
   (`uiOk_call`, `siOk_call`) take it. Needed of W0: `kvHandle` records its client (or `NewKV`'s post
   gives `kvHandle kv c γ who`) and `kvHandle_kvAt` takes `clientReady c`; `retryKVHandle_remoteKVAt`
   likewise. 1c gives `isClient_ready`, `clientMut_ready`, `clientRest_ready`, `clientReady_null`.
   ```go
   client.KV = NewKV(client)   // client.go: before client.Auth = NewAuth(client)
   ```
   Used by: `Client.unaryClientInterceptor.spec`, `newClient.spec`.
2. **`isClient_conn`/`clientRest_conn` are false of an in-process client** (`v3client.New`:
   `NewCtxClient`, no connection; its fields set from adapters): 1c's `clientBare_assemble` gives
   `isClient c γ none` for it, which cannot give `clientConnOk` (no `conn`). Request: drop
   `isClient_conn`/`clientRest_conn` (their only use is `NewKV(c)` inside `newClient`, where 1c's
   `clientCore` gives `clientConnOk`, `clientConnOk_core`), or index `isClient` by whether it has a
   connection.
   Used by: `clientBare_assemble`, snippet `clientv3client/inproc.go`.
3. **A context carrying a token no provider issued** (`examples/etcd/auth`'s `bad` principal:
   `metadata.AppendToOutgoingContext(ctx, "token", badToken)`): an introduction
   `ctxTokenMd ctx tok ∗ tokenUnissued γ tok ⊢ ctxPrin dflt ctx p` for every `p` (the server refuses
   with `ErrInvalidAuthToken`, a refusal at any principal), with `tokenUnissued` 3d's (the token
   providers issue only tokens they generate). Used by: snippet `clientv3client/auth.go`
   (`ReqRefusedPrincipals`).
4. **Repeatable writes** (provability review S3): `top.md` and `Api.lean`'s header should say a
   write is fired at most once *unless repeatable*: `LeaseGrant`, `LeaseRevoke`, `Alarm` (disarm)
   are sent with `withRepeatablePolicy()` and take persistent updates (1c's `CallTriple`,
   `reqRetryRep`). (W0's round 3 second part did this for `top.md`; the `Api.lean` header too.)
