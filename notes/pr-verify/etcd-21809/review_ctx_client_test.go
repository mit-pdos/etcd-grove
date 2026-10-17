package clientv3_test

// Reviewer probes for etcd-io/etcd#21809: what a NewCtxClient caller, who owns the grpc
// connection, can do with dial-level default call options and interceptors, at base and head.

import (
	"context"
	"net"
	"strings"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/test/bufconn"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

type rvKV struct{ pb.UnimplementedKVServer }

func (rvKV) Put(context.Context, *pb.PutRequest) (*pb.PutResponse, error) {
	return &pb.PutResponse{Header: &pb.ResponseHeader{}}, nil
}
func (rvKV) Range(_ context.Context, r *pb.RangeRequest) (*pb.RangeResponse, error) {
	return &pb.RangeResponse{Header: &pb.ResponseHeader{},
		Kvs: []*mvccpb.KeyValue{{Key: r.Key, Value: make([]byte, 5<<20)}}, Count: 1}, nil
}

func rvKVClient(t *testing.T, dialOpts ...grpc.DialOption) clientv3.KV {
	lis := bufconn.Listen(1 << 20)
	s := grpc.NewServer(grpc.MaxRecvMsgSize(64<<20), grpc.MaxSendMsgSize(64<<20))
	pb.RegisterKVServer(s, rvKV{})
	go s.Serve(lis)
	t.Cleanup(s.Stop)
	opts := append([]grpc.DialOption{
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()),
	}, dialOpts...)
	conn, err := grpc.NewClient("passthrough:///bufnet", opts...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	c := clientv3.NewCtxClient(context.Background())
	t.Cleanup(func() { c.Close() })
	return clientv3.NewKVFromKVClient(pb.NewKVClient(conn), c)
}

// Base: the caller CAN already raise the receive limit on its own connection (contra the PR text).
func TestReviewDialRecvLimit(t *testing.T) {
	kv := rvKVClient(t, grpc.WithDefaultCallOptions(grpc.MaxCallRecvMsgSize(64<<20)))
	if _, err := kv.Get(context.Background(), "k"); err != nil {
		t.Fatalf("Get 5MiB with dial recv limit 64MiB: %v", err)
	}
}

// A caller that deliberately LOWERS its receive limit (1 MiB) on its connection: at head the
// per-call MaxInt32 overrides it, so the 5 MiB response is accepted.
func TestReviewDialRecvLimitLowered(t *testing.T) {
	kv := rvKVClient(t, grpc.WithDefaultCallOptions(grpc.MaxCallRecvMsgSize(1<<20)))
	_, err := kv.Get(context.Background(), "k")
	t.Logf("Get 5MiB with dial recv limit 1MiB: err=%v", err)
	if err == nil {
		t.Fatalf("caller's 1 MiB receive limit was overridden")
	}
}

// Head: the caller's dial-level WaitForReady(false) no longer gives fail-fast.
func TestReviewDialFailFast(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	lis.Close()
	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()),
		grpc.WithDefaultCallOptions(grpc.WaitForReady(false)))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	c := clientv3.NewCtxClient(context.Background())
	defer c.Close()
	kv := clientv3.NewKVFromKVClient(pb.NewKVClient(conn), c)
	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
	defer cancel()
	start := time.Now()
	_, err = kv.Put(ctx, "k", "v")
	d := time.Since(start)
	t.Logf("Put: %v after %v", err, d.Round(100*time.Millisecond))
	if d > 500*time.Millisecond {
		t.Fatalf("dial-level WaitForReady(false) ignored: blocked %v", d)
	}
}

// Head workaround: an interceptor appending a larger send limit after the per-call options.
func TestReviewInterceptorSendLimit(t *testing.T) {
	kv := rvKVClient(t, grpc.WithChainUnaryInterceptor(func(ctx context.Context, m string, req, rep any,
		cc *grpc.ClientConn, inv grpc.UnaryInvoker, opts ...grpc.CallOption) error {
		return inv(ctx, m, req, rep, cc, append(opts, grpc.MaxCallSendMsgSize(64<<20))...)
	}))
	if _, err := kv.Put(context.Background(), "k", strings.Repeat("x", 3<<20)); err != nil {
		t.Fatalf("Put 3MiB with interceptor raising the send limit: %v", err)
	}
}
