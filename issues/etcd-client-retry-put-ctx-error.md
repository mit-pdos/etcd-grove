# clientv3: the retry interceptor retries a Put (any non-repeatable RPC) after a `Canceled` or `DeadlineExceeded` status while the caller's context is live

- **Status**: open (not filed; a robustness issue: a write may be applied twice, on a path that
  needs a `Canceled`/`DeadlineExceeded` status to reach the client while the caller's context is
  not done).
- **Where**: `client/v3/retry_interceptor.go:76-83` (`unaryClientInterceptor`: `if
  isContextError(lastErr) { if ctx.Err() != nil { return lastErr }; continue }`, with the comment
  "its the callCtx deadline or cancellation, in which case try again"), before the policy check
  `isSafeRetry` (`retry_interceptor.go:86-96`, which for a `nonRepeatable` call is
  `isSafeRetryMutableRPC`, `retry.go:78-93`: "Returning "false" means retry should stop,
  otherwise it violates write-at-most-once semantics"); the interceptor is installed with
  `withMax(defaultUnaryMaxRetries)` (100, `options.go:45`, `client.go:270`) for every unary call,
  `kv.Put`'s included (`retryKVClient.Put` passes no policy: `nonRepeatable`, the default). Upstream
  etcd at the fork's pinned revision (`bc8b52a50`, `etc/goose.py`).
- **What happens**: when an attempt of a unary RPC fails with a gRPC status `Canceled` or
  `DeadlineExceeded` and the caller's context is not done, the interceptor retries the call,
  whatever its retry policy: a `Put`, `DeleteRange` or `Txn` is sent again. The "callCtx" the
  comment refers to is go-grpc-middleware's per-attempt context (its `perCallTimeout`), which
  etcd's fork of the interceptor dropped: no per-call context remains, so the branch is reached
  only by a status that does not come from the caller's context: one the server returns (etcd's
  server answers a proposal whose context was canceled with `rpctypes.ErrGRPCCanceled`,
  `codes.Canceled`, `v3rpc/util.go`'s `errors.ErrCanceled` entry; a range whose context's deadline
  passed with `codes.DeadlineExceeded`), one a proxy in between returns (etcd's gRPC proxy, an L7
  load balancer), or the gRPC client's own (`ErrClientConnClosing` is `codes.Canceled`). If the
  first attempt reached the server and was applied, the retry applies the write a second time
  (a `Put` of the same key and value: a second revision, a second watch event; a `Txn` is
  re-evaluated). Reproduction (a test in package `clientv3`; it fails: the mock server receives
  the `Put` twice):

```go
package clientv3

import (
	"context"
	"net"
	"sync/atomic"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// putCountingKV applies every Put it receives (counts it), and answers the first one with a
// gRPC Canceled status, as a server whose handler context was canceled after the write was
// applied would (etcd's server maps a canceled proposal to rpctypes.ErrGRPCCanceled).
type putCountingKV struct {
	pb.UnimplementedKVServer
	puts atomic.Int32
}

func (s *putCountingKV) Put(ctx context.Context, r *pb.PutRequest) (*pb.PutResponse, error) {
	if s.puts.Add(1) == 1 {
		return nil, status.Error(codes.Canceled, "etcdserver: request canceled")
	}
	return &pb.PutResponse{Header: &pb.ResponseHeader{Revision: 2}}, nil
}

func TestPutRetriedAfterCanceledStatus(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer lis.Close()
	srv := grpc.NewServer()
	kvs := &putCountingKV{}
	pb.RegisterKVServer(srv, kvs)
	go srv.Serve(lis)
	defer srv.Stop()

	c, err := New(Config{Endpoints: []string{lis.Addr().String()}, DialTimeout: 5 * time.Second})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	if _, err := c.Put(ctx, "k", "v"); err != nil {
		t.Fatalf("Put: %v", err)
	}
	if n := kvs.puts.Load(); n != 1 {
		t.Errorf("the server received the Put %d times: the client retried a non-repeatable request", n)
	}
}
```

  Run 2026-10-14 (`GOTOOLCHAIN=go1.27.1 go test -run TestPutRetriedAfterCanceledStatus` in
  `client/v3`): `the server received the Put 2 times`; the client's log shows `retrying of unary
  invoker failed ... code = Canceled desc = etcdserver: request canceled`, and `Put` returns
  success.
- **Expected**: `isSafeRetryMutableRPC`'s write-at-most-once: a non-repeatable RPC is retried only
  when the request was not sent (no connection, no address available). Neither the `KV.Put`
  documentation nor the interceptor's says that a successful `Put` may have been applied more than
  once.
- **How the proof handles it**: the transport contract (`Spec/google_golang_org/grpc/
  ClientConn__Invoke.lean`, `grpc.ClientConn.invokePutSpec`) says only that a successful reply is
  the last run's (the server's handler may have run before, a failed attempt may have been
  applied), and the end-to-end result (`client/v3/Results.lean`, `client_put_end_to_end`) says what
  that run did, nothing about other runs. A cluster-level contract (unit C2, `notes/STATUS.md`)
  must allow a successful `Put` to be preceded by applications of the same put.
- **Possible fixes**: in the `isContextError` branch, retry only a repeatable call
  (`callOpts.retryPolicy == repeatable`), or drop the branch (no per-call context exists:
  return `lastErr` if `ctx.Err() != nil`, else fall through to `isSafeRetry`, which already
  returns false for a context error: `isSafeRetry`'s first check).
- **Found**: 2026-10-14, unit C1 (the client meets the server), stating the transport contract
  (reading `retry_interceptor.go` for when a `Put` is retried).
