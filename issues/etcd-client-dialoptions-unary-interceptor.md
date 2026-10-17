---
upstream: none
checked: 2026-10-16
links:
---

# clientv3: a `grpc.WithUnaryInterceptor` in `Config.DialOptions` silently replaces the client's retry interceptor

- **Status**: open (not filed; documentation: `Config.DialOptions` invites interceptors, without
  saying that only `grpc.WithChainUnaryInterceptor` keeps the client's own).
- **Where**: `client/v3/config.go:82` ("DialOptions is a list of dial options for the grpc client
  (e.g., for interceptors)"); `client/v3/client.go:270` (`dialSetupOpts`:
  `grpc.WithUnaryInterceptor(c.unaryClientInterceptor(withMax(unaryMaxRetries), rrBackoff))`),
  `client.go:325` (`dial`: `opts = append(opts, c.cfg.DialOptions...)`, after it); grpc's
  `WithUnaryInterceptor` (`dialoptions.go`, v1.84.0: it sets `dopts.unaryInt`, so the last one
  given wins). Upstream etcd at the fork's pinned revision (`bc8b52a50`, `etc/goose.py`).
- **What happens**: a caller who passes its own unary interceptor with `grpc.WithUnaryInterceptor`
  in `Config.DialOptions` (as the field's documentation suggests) replaces the client's retry
  interceptor: unary calls are no longer retried (a `Get` fails on a transient `Unavailable`),
  the auth token is no longer refreshed on `ErrInvalidAuthToken`/`ErrUserEmpty`, the API-version
  metadata (`withVersion`) is no longer added, and `MaxUnaryRetries`/`BackoffWaitBetween` have no
  effect; nothing reports it. `grpc.WithChainUnaryInterceptor` composes after the client's
  interceptor and keeps it. Reproduction (a test in package `clientv3`; it fails on the
  `WithUnaryInterceptor` case: the server receives the `Range` once and the `Get` returns
  `Unavailable`):

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

// unavailableOnceKV answers the first Range with Unavailable, the next ones normally: a
// transient failure the client's retry interceptor retries for a Range (repeatable).
type unavailableOnceKV struct {
	pb.UnimplementedKVServer
	ranges atomic.Int32
}

func (s *unavailableOnceKV) Range(ctx context.Context, r *pb.RangeRequest) (*pb.RangeResponse, error) {
	if s.ranges.Add(1) == 1 {
		return nil, status.Error(codes.Unavailable, "transient")
	}
	return &pb.RangeResponse{Header: &pb.ResponseHeader{Revision: 1}}, nil
}

func getWithDialOptions(t *testing.T, opts ...grpc.DialOption) (int32, error) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer lis.Close()
	srv := grpc.NewServer()
	kvs := &unavailableOnceKV{}
	pb.RegisterKVServer(srv, kvs)
	go srv.Serve(lis)
	defer srv.Stop()

	c, err := New(Config{Endpoints: []string{lis.Addr().String()}, DialTimeout: 5 * time.Second,
		DialOptions: opts})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	_, err = c.Get(ctx, "k")
	return kvs.ranges.Load(), err
}

func TestDialOptionsUnaryInterceptorReplacesRetry(t *testing.T) {
	n, err := getWithDialOptions(t)
	if err != nil || n != 2 {
		t.Fatalf("without DialOptions: %d ranges, err %v; want 2, nil (one retry)", n, err)
	}
	logging := func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn,
		invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {
		return invoker(ctx, method, req, reply, cc, opts...)
	}
	n, err = getWithDialOptions(t, grpc.WithChainUnaryInterceptor(logging))
	if err != nil || n != 2 {
		t.Errorf("with a WithChainUnaryInterceptor dial option: %d ranges, err %v; want 2, nil", n, err)
	}
	n, err = getWithDialOptions(t, grpc.WithUnaryInterceptor(logging))
	if err != nil || n != 2 {
		t.Errorf("with a WithUnaryInterceptor dial option: %d ranges, err %v; want 2, nil", n, err)
	}
}
```

  Run 2026-10-14 (`go test -run TestDialOptionsUnaryInterceptorReplacesRetry`, go 1.27.1):
  `with a WithUnaryInterceptor dial option: 1 ranges, err rpc error: code = Unavailable desc =
  transient; want 2, nil`; the `WithChainUnaryInterceptor` case passes.
- **Expected**: either the documentation says to use `grpc.WithChainUnaryInterceptor` (a
  `WithUnaryInterceptor` replaces the client's retry interceptor), or the client installs its
  interceptor with `grpc.WithChainUnaryInterceptor` so that a caller's `WithUnaryInterceptor`
  (which grpc runs first) does not remove it.
- **How the proof handles it** (2026-10-17, item 5): `clientv3.New` is now proved
  (`Spec/go_etcd_io/etcd/client/v3/New.lean`) under the configuration premise that
  `Config.DialOptions` is empty (`clientCfgOk`), which excludes such an interceptor; grpc's
  `NewClient` axiom (`Spec/google_golang_org/grpc/NewClient.lean`) composes the chain from the
  options' descriptors (the last `WithUnaryInterceptor` wins). Before: the client's results took
  the connection as a premise,
  `isEtcdConn conn addr` (`Proof/go_etcd_io/etcd/client/v3/InvKVConn.lean`): grpc's connection
  with exactly one unary interceptor, one meeting the retry interceptor's contract
  (`etcdInterceptorOk`, which `Client.unaryClientInterceptor` returns:
  `Proof/go_etcd_io/etcd/client/v3/Client__unaryClientInterceptor.lean`), and no default call
  options: `clientv3.New` given no `DialOptions` that add interceptors or call options (an
  assumption about the unverified constructor). The generic gRPC contract
  (`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`) states the chain as grpc composes it,
  so another configuration would be another premise.
- **Possible fixes**: document it on `Config.DialOptions`; or `dialSetupOpts` uses
  `grpc.WithChainUnaryInterceptor` for the retry interceptor (and the stream one), so that a
  caller's interceptors compose with it.
- **Found**: 2026-10-14, unit P3a (moving the gRPC trust boundary below the retry interceptor:
  stating which interceptor chain the client's connection has).

**The stream interceptor too** (unit W-W, 2026-10-15; by reading, not reproduced): `dialSetupOpts`
also installs `grpc.WithStreamInterceptor(c.streamClientInterceptor(withMax(0), rrBackoff))`, and
grpc's `WithStreamInterceptor` likewise keeps only the last one given; a
`grpc.WithStreamInterceptor` in `Config.DialOptions` replaces it, so watch streams lose
`withVersion`'s metadata and `getToken` (the token refresh on reconnect that etcd-io/etcd#11954
added). `grpc.ClientConn.NewStream`'s axiom (`Spec/google_golang_org/grpc/ClientConn__NewStream.lean`)
assumes the client's own stream interceptor.
