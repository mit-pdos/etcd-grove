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
