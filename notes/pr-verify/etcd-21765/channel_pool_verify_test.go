package clientv3

import (
	"context"
	"errors"
	"net"
	"testing"

	"go.etcd.io/etcd/client/v3/internal/resolver"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
)

// TestVerify_Finding1_SetEndpointsEmptyChannelsInNewClient reproduces Finding 1:
// SetEndpoints iterates over c.channels without updating c.resolver directly.
// In newClient (client.go:471), client.SetEndpoints(cfg.Endpoints...) is called
// when client.channels is still an empty map (before client.channels[defaultChannelKey]
// is populated at line 483), so SetEndpoints executes 0 loop iterations and
// fails to update client.resolver.
func TestVerify_Finding1_SetEndpointsEmptyChannelsInNewClient(t *testing.T) {
	r := resolver.New()
	defer r.Close()

	c := NewCtxClient(context.Background())
	c.resolver = r
	c.channels = make(map[string]channel)

	// Mirrors newClient line 471: SetEndpoints called before c.channels["default"] is populated.
	c.SetEndpoints("127.0.0.1:2379", "127.0.0.1:2380")

	if got := c.Endpoints(); len(got) != 2 {
		t.Fatalf("expected 2 endpoints on client, got %v", got)
	}
	// Once populated at line 483, c.channels["default"] points to c.resolver,
	// which never received SetEndpoints("127.0.0.1:2379", "127.0.0.1:2380") at line 471.
	t.Logf("After SetEndpoints on empty c.channels (as at newClient:471): c.Endpoints()=%v, len(c.channels)=%d (0 resolver updates performed)",
		c.Endpoints(), len(c.channels))
}

// TestVerify_Finding2a_RetryKVClientNilEpMuPanic reproduces Finding 2a:
// RetryKVClient(c) wraps c in &routingClientConn{client: c}. If c.epMu == nil
// (e.g., a struct literal &Client{conn: conn}), any KV RPC panics in c.epMu.RLock().
func TestVerify_Finding2a_RetryKVClientNilEpMuPanic(t *testing.T) {
	conn, err := grpc.NewClient("passthrough:///127.0.0.1:0",
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatalf("grpc.NewClient: %v", err)
	}
	defer conn.Close()

	c := &Client{conn: conn}
	rkv := RetryKVClient(c)

	panicked := false
	func() {
		defer func() {
			if r := recover(); r != nil {
				panicked = true
				t.Logf("Recovered expected panic on RetryKVClient(&Client{conn: conn}): %v", r)
			}
		}()
		_, _ = rkv.Put(context.Background(), nil)
	}()
	if !panicked {
		t.Fatalf("expected nil-pointer panic when c.epMu == nil")
	}
}

// TestVerify_Finding2b_NewCtxClientDirectConnBroken reproduces Finding 2b:
// A client created with NewCtxClient(ctx) + c.conn = conn + c.KV = NewKV(c)
// has c.channels == nil, so all KV RPCs fail with connectionPoolClosedError()
// instead of falling back to c.conn.
func TestVerify_Finding2b_NewCtxClientDirectConnBroken(t *testing.T) {
	conn, err := grpc.NewClient("passthrough:///127.0.0.1:0",
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatalf("grpc.NewClient: %v", err)
	}
	defer conn.Close()

	c := NewCtxClient(context.Background())
	c.conn = conn
	c.KV = NewKV(c)

	_, err = c.KV.Get(context.Background(), "k")
	if err == nil {
		t.Fatalf("expected error from NewCtxClient with c.channels == nil")
	}
	t.Logf("NewCtxClient with c.conn != nil but c.channels == nil returned error: %v (code=%v)",
		err, status.Code(err))
}

// TestVerify_Finding3_ClosedClientErrorTypeRegressionAndDeadCode reproduces Finding 3:
// Because Close() calls c.cancel() before setting c.channels = nil, c.ctx.Err()
// is always context.Canceled after Close(). Thus connectionPoolClosedError()
// always returns context.Canceled (codes.Unknown) instead of
// status.Error(codes.Canceled, "etcdclient: client connection is closing") (codes.Canceled).
func TestVerify_Finding3_ClosedClientErrorTypeRegressionAndDeadCode(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("net.Listen: %v", err)
	}
	defer lis.Close()
	srv := grpc.NewServer()
	go func() { _ = srv.Serve(lis) }()
	defer srv.Stop()

	c, err := New(Config{
		Endpoints: []string{lis.Addr().String()},
	})
	if err != nil {
		t.Fatalf("New: %v", err)
	}

	if err := c.Close(); err != nil {
		t.Fatalf("1st Close: %v", err)
	}

	poolErr := c.connectionPoolClosedError()
	t.Logf("After Close(), connectionPoolClosedError() = %T (%v), status.Code = %v",
		poolErr, poolErr, status.Code(poolErr))
	if !errors.Is(poolErr, context.Canceled) {
		t.Fatalf("expected context.Canceled, got %v", poolErr)
	}
	if status.Code(poolErr) != codes.Unknown {
		t.Fatalf("expected status.Code == codes.Unknown (regression from codes.Canceled), got %v", status.Code(poolErr))
	}

	_, getErr := c.Get(context.Background(), "k")
	t.Logf("After Close(), c.Get(context.Background(), \"k\") = %T (%v), status.Code = %v",
		getErr, getErr, status.Code(getErr))
}

// TestVerify_Finding4_CloseNotIdempotentAndErrorsJoinMasksIsConnCanceled reproduces Finding 4:
// 1. Calling c.Close() a second time returns context.Canceled (with IsConnCanceled == false)
//    whereas the first call returns nil.
// 2. When errors.Join combines a non-Canceled gRPC error from one channel with a Canceled
//    error from another channel, status.FromError inspects only the first gRPC status error,
//    causing IsConnCanceled to return false.
func TestVerify_Finding4_CloseNotIdempotentAndErrorsJoinMasksIsConnCanceled(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("net.Listen: %v", err)
	}
	defer lis.Close()
	srv := grpc.NewServer()
	go func() { _ = srv.Serve(lis) }()
	defer srv.Stop()

	c, err := New(Config{
		Endpoints: []string{lis.Addr().String()},
	})
	if err != nil {
		t.Fatalf("New: %v", err)
	}

	err1 := c.Close()
	err2 := c.Close()
	t.Logf("1st Close() = %v; 2nd Close() = %v", err1, err2)
	if err1 != nil {
		t.Fatalf("expected 1st Close() == nil, got %v", err1)
	}
	if !errors.Is(err2, context.Canceled) {
		t.Fatalf("expected 2nd Close() == context.Canceled, got %v", err2)
	}

	otherGrpcErr := status.Error(codes.Internal, "transport close error")
	rawCancelErr := status.Error(codes.Canceled, "etcdclient: client connection is closing")
	joinedErr := errors.Join(otherGrpcErr, rawCancelErr)
	t.Logf("IsConnCanceled(rawCancelErr)=%v, IsConnCanceled(errors.Join(otherGrpcErr, rawCancelErr))=%v (code=%v)",
		IsConnCanceled(rawCancelErr), IsConnCanceled(joinedErr), status.Code(joinedErr))
	if !IsConnCanceled(rawCancelErr) {
		t.Fatalf("expected IsConnCanceled(rawCancelErr) == true")
	}
	if IsConnCanceled(joinedErr) {
		t.Fatalf("expected IsConnCanceled(joinedErr) == false when first channel error is non-Canceled")
	}
}

// TestVerify_Finding6_ErrChannelKeyNotFoundWrappedIsNotLeaf reproduces Finding 6:
// connectionForContext returns fmt.Errorf("%w: %q", ErrChannelKeyNotFound, key),
// which is a *fmt.wrapError with a non-nil Unwrap() method (not a leaf error).
func TestVerify_Finding6_ErrChannelKeyNotFoundWrappedIsNotLeaf(t *testing.T) {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("net.Listen: %v", err)
	}
	defer lis.Close()
	srv := grpc.NewServer()
	go func() { _ = srv.Serve(lis) }()
	defer srv.Stop()

	c, err := New(Config{
		Endpoints: []string{lis.Addr().String()},
	})
	if err != nil {
		t.Fatalf("New: %v", err)
	}
	defer c.Close()

	ctx := WithChannelKey(context.Background(), "unconfigured")
	_, err = c.connectionForContext(ctx)
	if !errors.Is(err, ErrChannelKeyNotFound) {
		t.Fatalf("expected ErrChannelKeyNotFound, got %v", err)
	}
	unwrapped := errors.Unwrap(err)
	t.Logf("connectionForContext error = %T (%v), errors.Unwrap(err) = %T (%v)",
		err, err, unwrapped, unwrapped)
	if unwrapped == nil {
		t.Fatalf("expected wrapped error (non-leaf), got nil Unwrap()")
	}
}
