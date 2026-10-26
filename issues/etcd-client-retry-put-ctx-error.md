---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#18424 issue closed: same root cause (ahrtr named the isContextError retry branch as unsafe for writes); closed not planned, maintainers judged it unreachable because ErrCanceled had no gRPC mapping
  - etcd-io/etcd#21122 pr merged: related, not this bug; added the errors.ErrCanceled -> codes.Canceled mapping (2026-02), which makes the branch reachable from the server, against #18424's reasoning
---

# clientv3: the retry interceptor retries a Put (any non-repeatable RPC) after a `Canceled` or `DeadlineExceeded` status while the caller's context is live

- **Status**: **fixed in the fork** (2026-10-18): in the `isContextError` branch a `nonRepeatable`
  call returns its attempt's error (`if callOpts.retryPolicy == nonRepeatable { return lastErr }`),
  with the reproduction below as a test (`client/v3/retry_put_ctx_error_test.go`), on
  `upamanyus/etcd` `goose-lean` as `8a24be2a3` (etc/goose.py's etcd pin since then; upstream main
  unchanged). At upstream's code: a robustness issue (not filed): a write may be applied twice, on
  a path that needs a `Canceled`/`DeadlineExceeded` status to reach the client while the caller's
  context is not done.
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
- **How it happens**: the retry loop has a policy check, `isSafeRetry`, that stops a mutable RPC
  from being retried once the request may have been sent. A context-error branch above it
  `continue`s the loop for any method and any retry policy, so for a `Canceled` or
  `DeadlineExceeded` status the check is never reached. In the reproduction above:

  1. The caller runs `c.Put(ctx, "k", "v")` with a live 10-second context. `retryKVClient.Put`
     passes no retry policy, so the call is `nonRepeatable`, with up to 100 attempts.
  2. Attempt 0 reaches the server, which applies the put (counts it) and answers
     `status.Error(codes.Canceled, "etcdserver: request canceled")`, the status etcd's server
     gives a proposal whose context was canceled (`rpctypes.ErrGRPCCanceled`).
  3. `isContextError(lastErr)` is true (`codes.Canceled`) and `ctx.Err()` is nil, so the loop
     `continue`s without calling `isSafeRetry`.
  4. Attempt 1 sends the same `Put` again. The server applies it a second time and answers
     success.
  5. `Put` returns success to the caller. The server received the `Put` twice.

  ```go
  // client/v3/retry_interceptor.go:54-98 (etcd main f061acd09), unaryClientInterceptor's loop
  		for attempt := uint(0); attempt < callOpts.max; attempt++ {
  			// ...
  			lastErr = invoker(ctx, method, req, reply, cc, grpcOpts...)
  			if lastErr == nil {
  				return nil
  			}
  			// ...
  			if isContextError(lastErr) { // <- codes.Canceled or codes.DeadlineExceeded
  				if ctx.Err() != nil {
  					// its the context deadline or cancellation.
  					return lastErr
  				}
  				// its the callCtx deadline or cancellation, in which case try again.
  				continue // <- any method, any retry policy
  			}
  			// ... token refresh ...
  			if !isSafeRetry(c, lastErr, callOpts) { // <- never reached for a context error
  				return lastErr
  			}
  ```

  ```go
  // client/v3/retry.go:77-94 (etcd main f061acd09): the policy that branch bypasses
  // isSafeRetryMutableRPC returns "true" when a mutable request is safe for retry.
  //
  // mutable requests (e.g. Put, Delete, Txn) should only be retried
  // when the status code is codes.Unavailable when initial connection
  // has not been established (no endpoint is up).
  //
  // Returning "false" means retry should stop, otherwise it violates
  // write-at-most-once semantics.
  func isSafeRetryMutableRPC(err error) bool {
  	if ev, ok := status.FromError(err); ok && ev.Code() != codes.Unavailable {
  		// ...
  		return false
  	}
  	desc := rpctypes.ErrorDesc(err)
  	return desc == "there is no address available" || desc == "there is no connection available"
  }
  ```
- **Expected**: `isSafeRetryMutableRPC`'s write-at-most-once: a non-repeatable RPC is retried only
  when the request was not sent (no connection, no address available). Neither the `KV.Put`
  documentation nor the interceptor's says that a successful `Put` may have been applied more than
  once.
- **How the proof handles it**: the transport contract (`Spec/google_golang_org/grpc/
  ClientConn__Invoke.lean`, `grpc.ClientConn.invokePutSpec`) says only that a successful reply is
  the last run's (the server's handler may have run before, a failed attempt may have been
  applied), and the end-to-end result (`client/v3/Results.lean`, `client_put_end_to_end`) says what
  that run did, nothing about other runs. A cluster-level contract (unit C2, `notes/STATUS.md`)
  must allow a successful `Put` to be preceded by applications of the same put. Since the fork's
  fix the interceptor's proof (`Proof/go_etcd_io/etcd/client/v3/Client__unaryClientInterceptor.lean`)
  covers the new return with its spec unchanged (the contract already allows an error return); the
  specs do not yet state the at-most-once resend, so the transport contract's allowance stays.
- **Possible fixes**: in the `isContextError` branch, retry only a repeatable call
  (`callOpts.retryPolicy == repeatable`), or drop the branch (no per-call context exists:
  return `lastErr` if `ctx.Err() != nil`, else fall through to `isSafeRetry`, which already
  returns false for a context error: `isSafeRetry`'s first check).
- **Found**: 2026-10-14, unit C1 (the client meets the server), stating the transport contract
  (reading `retry_interceptor.go` for when a `Put` is retried).
