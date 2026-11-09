# Requirements on `go.etcd.io/etcd/client/v3/concurrency` (batch 1d)

## from 1f

The recipes' `DoubleBarrier` and `RWMutex` (and `newEphemeralKV`) take a `*concurrency.Session`.
Their `Api.lean` names it through a slot, `Recipes.sessionAt s γ who id` (persistent), which 1d's
`Concurrency.isSession s γ who id` (same signature) replaces at integration.

1. **`s.Client()`** returns a client `c` with `isClient c γ who` (1d's `isSession_client` gives the
   field; a `Session.Client.spec` returning it is what the recipes call).
2. **`s.Lease()`** returns the lease `id` the session's predicate names. Nothing about its
   liveness is needed: a put with a lease no longer alive is `ErrLeaseNotFound`, a linearized
   answer of W0's model.
   ```go
   k, err := newKV(s.Client().KV, key, val, s.Lease())
   ```
   Used by: `newEphemeralKV.spec` (so `newUniqueEphemeralKV`, `newUniqueEphemeralKey`,
   `DoubleBarrier.Enter`, `RWMutex.Lock`, `RLock`), `DoubleBarrier.Leave`,
   `RWMutex.waitOnLastRev` (`s.Client()`).
3. Both persistent, callable from any goroutine (the recipes' tests share one session among ten
   goroutines' barriers).

## from 1e

The leasing KV's session monitor (`client/v3/leasing/kv.go:138`, `monitorSession`) makes a new
session whenever the last one is done, in a background goroutine, and reads it under its cache's
lock from any goroutine.

1. **`NewSession(cl, opts...)`** for a client `isClient cl γ who` and the options in 1e's slot
   `Leasing.sessOptsOk osl cl` (`Spec/go_etcd_io/etcd/client/v3/leasing/Api.lean`; realize it as
   your session-options bundle and prove `sessOptsOk_nil`: the proxy passes none; the tests pass
   `WithTTL(1)`): a session (persistent handle) or an error, no panic. Its lease grant and the
   lessor's keep-alives are steps on `etcdState γ`: take them as updates the caller can build from a
   **persistent** update covering any `leaseGrant`/`leaseKeepAlive` step of `who` (1e fires them
   from `Leasing.protoUpd γ who pfx`, whose `ProtoStep` allows exactly those and writes under the
   prefix); it is called again and again, so nothing once-only per call beyond that.
   ```go
   s, err := concurrency.NewSession(lkv.cl, lkv.sessionOpts...)
   if err != nil { continue }
   lkv.session = s; close(lkv.sessionc)
   ```
   Used by: `leasingKV.monitorSession.spec`.
2. **`s.Lease()`**: the session's lease id (any `w64`), persistent handle only; **`s.Done()`**: a
   channel one may receive from (closed when the keep-alive ends, or never), any number of times
   from any goroutine, non-blocking `select` included.
   ```go
   select { case <-lkv.session.Done(): default: return true }
   return lkv.session.Lease()
   ```
   Used by: `leasingKV.readySession.spec`, `leasingKV.leaseID.spec`, `monitorSession`.
