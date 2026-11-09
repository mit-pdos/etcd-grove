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
