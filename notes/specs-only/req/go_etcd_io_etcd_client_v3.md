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
   caller's update with that refusal itself; a repeatable call (a read, `withRepeatablePolicy`) is resent after
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
