---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#15539 issue closed: this bug (closed by the stale bot, not fixed)
  - etcd-io/etcd#15540 pr closed: adds EtcdError.GRPCStatus with tests; closed unmerged
---

# clientv3: `rpctypes.EtcdError` has no `GRPCStatus`, so a watch on an auth client halts on a transient leader change

- **Status**: open bug (a transient error is treated as permanent; also wrong status codes in
  metrics and for any caller that uses `status.FromError` on a client error).
- **Where**: `api/v3rpc/rpctypes/error.go:241-254` (`EtcdError`: `Code()` and `Error()`, no
  `GRPCStatus()`); `client/v3/client.go:606` (`ContextError` converts through `rpctypes.Error`);
  `client/v3/auth.go:138` (`Authenticate` returns `ContextError(ctx, err)`);
  `client/v3/retry_interceptor.go:118` (`streamClientInterceptor` calls `c.getToken(ctx)` before
  every stream); `client/v3/watch.go:1057-1061` (`openWatchClient`: `if isHaltErr(w.ctx, err) {
  return nil, v3rpc.Error(err) }`); `client/v3/client.go:570` (`isHaltErr`: halts unless the code
  is `Unavailable` or `Internal`). Upstream etcd at the fork's pinned revision (`107edf7e4`,
  `etc/goose.py`).
- **What happens**: on a client with a user name and password, opening a watch stream first
  authenticates. If `Authenticate` fails with `ErrGRPCLeaderChanged` or `ErrGRPCNoLeader` (code
  `Unavailable`), the error comes back as an `EtcdError`. `status.FromError` cannot see its code
  and reports `Unknown`, so `isHaltErr` returns `true`. `openWatchClient` gives up, and `run`
  closes every watcher of the stream with the error instead of retrying with backoff. Reproduction
  (a test in package `clientv3`, `issues/etcd-client-etcderror-no-grpcstatus/halt_on_converted_error_test.go`;
  it fails at the pin):

```go
package clientv3

import (
	"context"
	"testing"

	"google.golang.org/grpc/status"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

func TestHaltOnConvertedLeaderChanged(t *testing.T) {
	ctx := context.Background()
	if isHaltErr(ctx, rpctypes.ErrGRPCLeaderChanged) {
		t.Fatalf("the gRPC error halts")
	}
	err := ContextError(ctx, rpctypes.ErrGRPCLeaderChanged) // what Authenticate returns
	t.Logf("converted: %T %v, code %v", err, err, status.Code(err))
	if isHaltErr(ctx, err) {
		t.Errorf("isHaltErr(ContextError(ErrGRPCLeaderChanged)) = true")
	}
}
```

  Run 2026-10-16 (`GOTOOLCHAIN=go1.27.1 go test -run TestHaltOnConvertedLeaderChanged` in
  `client/v3`): `converted: rpctypes.EtcdError etcdserver: leader changed, code Unknown`, then the
  failure.
- **Expected**: `openWatchClient` "retries opening a watch client until success or halt", and
  `isHaltErr` treats `Unavailable` as "the system will be right back". An error that was
  `Unavailable` on the wire should still be `Unavailable` after the client's conversion.
- **How the proof handles it**: `isHaltErr.spec` and `openWatchClient.spec` are stated over grpc's
  `statusCode`, which is opaque (`Spec/google_golang_org/grpc/status/FromError.lean:31`), so they
  admit halting on any error. `streamClientInterceptor` (where `getToken` runs) is not translated.
  The watch client is verified only for a stream that never reconnects (`noRetryableStreamErr`,
  `Proof/go_etcd_io/etcd/client/v3/InvWatch.lean:163`). Triage: `notes/bug-triage/etcd-15539.md`
  (proposal `client-error-status-codes`).
- **Possible fixes**: add `func (e EtcdError) GRPCStatus() *status.Status { return
  status.New(e.code, e.desc) }` (#15540). Alternatively, have `getToken` in the stream interceptor
  return the raw gRPC error.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#15539.
