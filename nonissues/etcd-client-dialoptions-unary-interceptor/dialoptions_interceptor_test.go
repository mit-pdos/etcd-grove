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
