---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#22710 issue open: a different race with SetEndpoints (dial() reading c.endpoints), not this one
  - etcd-io/etcd#13201 issue closed: the same kind of race in dialWithBalancer, fixed by #13203
blocks-proof: no
---

# clientv3: `SetEndpoints` races the client's first RPC (resolver `Build` vs `SetEndpoints`)

Calling `SetEndpoints` on a client while another goroutine makes an RPC that wakes the connection
(the client's first RPC, or the first after the connection went idle) is a data race inside the
client's resolver: `-race` reports it, and the resolver can be built from a torn endpoint list or
miss the service config. Auto-sync (`AutoSyncInterval > 0`) calls `SetEndpoints` periodically on
its own goroutine, so a client with auto-sync reaches it without calling `SetEndpoints` itself.

**Expected:** `SetEndpoints` should be safe to call concurrently with RPCs, as its locking of
`epMu` and auto-sync's use of it imply.

**Impact:** any client that changes its endpoints while in use: auto-sync users, and callers of
`SetEndpoints`. The window is each time the gRPC channel leaves idle mode: the first RPC after
`New` (the client dials with `grpc.NewClient`, whose channel starts idle), and every RPC after an
idle period (grpc's default idle timeout is 30 minutes). Seen under `-race` at the default
configuration.

**Reproduction:** `TestSetEndpointsRacesFirstRPC` in
[`issues/etcd-client-resolver-build-race/resolver_build_race_test.go`](etcd-client-resolver-build-race/resolver_build_race_test.go),
run as an external test of `go.etcd.io/etcd/client/v3` at upamanyus/etcd@a4d2bb1720b9 (the pinned
fork of etcd-io/etcd main, 2026-11-07; `client/v3/internal/resolver/resolver.go` is identical on
etcd-io/etcd main, checked 2026-11-09), grpc v1.84.0, go1.27.3 linux/amd64, with `-race` (from
`examples/`, in a test package there):

```
WARNING: DATA RACE
Write at 0x00c0003780e0 by goroutine 11:
  go.etcd.io/etcd/client/v3/internal/resolver.(*EtcdManualResolver).Build()
      .../client/v3/internal/resolver/resolver.go:44
  google.golang.org/grpc/internal/resolver/delegatingresolver.New()
  google.golang.org/grpc.(*ccResolverWrapper).start.func1()
  google.golang.org/grpc/internal/grpcsync.(*CallbackSerializer).run()
Previous read at 0x00c0003780e0 by goroutine 14:
  go.etcd.io/etcd/client/v3/internal/resolver.(*EtcdManualResolver).SetEndpoints()
      .../client/v3/internal/resolver/resolver.go:54
  go.etcd.io/etcd/client/v3.(*Client).SetEndpoints()
      .../client/v3/client.go:182
...
--- FAIL: TestSetEndpointsRacesFirstRPC (0.55s)
    testing.go:1867: race detected during execution of test
```

(Three races are reported: `Build` writing `serviceConfig` against `SetEndpoints`' copy of the
resolver, `Build` reading `endpoints` against `SetEndpoints` writing it, and `state()` on both
sides.)

**Cause:** grpc calls the resolver builder's `Build` when the channel exits idle mode, on its own
serializer goroutine. `EtcdManualResolver.Build` writes `r.serviceConfig` and reads `r.endpoints`
through `r.state()` ([`resolver.go`](https://github.com/etcd-io/etcd/blob/main/client/v3/internal/resolver/resolver.go#L43-L50));
`SetEndpoints` writes `r.endpoints` and copies the whole resolver for `updateState` (a value
receiver), reading `serviceConfig` (`resolver.go#L52-L61`). `Client.SetEndpoints` holds `c.epMu`
([`client.go`](https://github.com/etcd-io/etcd/blob/main/client/v3/client.go)), which `Build` does
not take, and nothing else orders the two.

## Proof

no: no top-level workload calls `SetEndpoints` or enables auto-sync (Kubernetes and the examples
never change endpoints). The client's specs (batch 1c) give the whole endpoints token
(`epsTok`) to `SetEndpoints` but let RPCs run concurrently, and grpc's boundary does not say when
it calls back into `Build`: the client's `SetEndpoints` spec (or the resolver's boundary) should
exclude a concurrent channel wake-up (found in the verification round's A2 review, S4; the request
is in `notes/specs-only/verify/repair-client-watch.md`).

## Fix

Not written. `EtcdManualResolver` should guard `endpoints` and `serviceConfig` with a mutex of its
own taken by `Build`, `SetEndpoints` and `state` (and `updateState` should take a pointer
receiver), or `Build` should not mutate the resolver (compute the service config into the state it
passes, keeping `serviceConfig` immutable after `New`).
