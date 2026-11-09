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
