# Files for the verification of etcd-io/etcd#21960

Revisions:
- **PR head**: `bd0d15a12bb0472a0f5441fc8973d7a367dfae53` (etcd-io/etcd, `pull/21960/head`).
- **Base**: `22d55b52acba4d981da3d139b6bc8912c7cadd18`, the PR's merge base with upstream `main`.
- **Fork**: `mit-pdos/etcd-grove` branch `pr-etcd-21960-goose-lean`, commit `0fe317c1a`: the PR on
  `goose-lean` `09669450f`, plus the PR's test with a `Leader()` added to its mock.

Toolchains: Go 1.26.4 for upstream checkouts. Go 1.27.1 for the fork. Under Go 1.27,
grpc v1.81.0 does not build against x/net v0.54.0 (`http2.TrailerPrefix`), so upstream
revisions need 1.26.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `lease_keepalive_noleader_test.go` | **F1.** The stream interceptor wraps a require-leader stream; `monitorLeader` then cancels the wrapper's context with `ErrGRPCNoLeader`. The client is idle. `LeaseKeepAlive` must return that error. It does at the base, and never returns at the PR head or on the fork branch. | base (passes), PR head (fails), fork (fails) | `cp lease_keepalive_noleader_test.go <checkout>/server/etcdserver/api/v3rpc/ && cd <checkout>/server && go test -count=1 -run TestLeaseKeepAliveReturnsOnNoLeader ./etcdserver/api/v3rpc/` |
| `lease_keepalive_grpc_review_test.go` | The reviewer's tests, over a real grpc server and client on loopback, with an interceptor that wraps the stream the way `newStreamInterceptor` does. `TestReviewClientCancelNoLeak`: on client cancellation neither version leaks. `TestReviewNoLeaderIdle`: **F1**, with the client idle. `TestReviewNoLeaderSendBlocked`: **F1b**, the handler blocked in `Send` on flow control. On the base, every test also checks that no `leaseKeepAlive` goroutine outlives the handler by more than 3s (**F2**). | base (all pass), PR head (`NoLeader*` fail) | `cp lease_keepalive_grpc_review_test.go <checkout>/server/etcdserver/api/v3rpc/ && cd <checkout>/server && go test -count=1 -v -run TestReview ./etcdserver/api/v3rpc/` |
| `base-tests.log`, `pr-head-tests.log` | **F1** with upstream's own integration tests. `TestV3LeaseKeepAliveForwardingCatchError/catches_NoLeader_error_with_WithRequireLeader` passes at the base and hangs until timeout at the PR head. `TestLeaseWithRequireLeader` passes at the base and fails at the PR head: the client's keep-alive ends with `Canceled` instead of `Unavailable` (no leader). Each log also has the output of `lease_keepalive_noleader_test.go`. | base, PR head | `cd <checkout>/tests && go test -count=1 -timeout 120s -v -run 'TestV3LeaseKeepAliveForwardingCatchError/catches_NoLeader_error_with_WithRequireLeader$' ./integration/` and `... -run 'TestLeaseWithRequireLeader$' ./integration/clientv3/lease/` |

**F2** (the PR's own test, `TestLeaseKeepAlive_GoroutineLeakOnDisconnect`, does not show a leak)
needs no extra file. Copy the PR head's `server/etcdserver/api/v3rpc/lease_test.go` onto the
base's unchanged `lease.go` and run `go test -count=1 -run TestLeaseKeepAlive_GoroutineLeakOnDisconnect ./etcdserver/api/v3rpc/`.
It passes there too (3 of 3 runs).
