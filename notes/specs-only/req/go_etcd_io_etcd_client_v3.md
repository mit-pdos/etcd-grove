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
   only after an attempt that was never sent (`isSafeRetryMutableRPC.spec`: `.notSent`), or after
   a refusal that fired nothing (a stale or invalid token: the interceptor refreshes it and
   resends; if it gives up, it fires the caller's update with that refusal, `EtcdErr.refusal`, or
   returns an indefinite error); a repeatable call (a read, `withRepeatablePolicy`) is resent after
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
   (its token's user, or none); a token refresh keeps it.
   Used by: every `KV.*Triple` (`Step who rq ...`).

5. **1b (watch)**: `OpWatch.spec` (W0's) builds the watch's `Op` (`opWatchM`, `watchPanics`);
   `watcherAt v γ who` is 1b's bundle; its events are the model's history (`KVHist.eventsAt`, the
   whole history kept, `compacted` the floor) and its compaction errors the model's
   (`EtcdErr.compacted`). `WithRequireLeader.spec` gives `ctxRequireLeader ctx'` (the server closes
   a watch whose member loses its leader). W0's KV specs say nothing of watches: no snippet of
   W0 relies on one.

6. **`ContextError`** is W0's (`ContextError.spec`, over `callErr`): 1b and 1c call it after their
   own gRPC calls, as `kv.go` does.
