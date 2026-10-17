// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package clientv3_test

// Probes for etcd-io/etcd#21809 (client/v3: NewCtxClient sets callOpts to defaultCallOpts).
// A KV built with NewKVFromKVClient over a NewCtxClient client, talking to a real gRPC server
// (in-memory, bufconn) whose own limits are large (64 MiB), so that only the client's limits
// matter. Run with `go test -run TestCtxClient -v .` in client/v3, at the upstream base and at
// the PR head.

import (
	"context"
	"net"
	"strings"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

const bigServerLimit = 64 << 20

type bigKVServer struct{ pb.UnimplementedKVServer }

func (bigKVServer) Put(_ context.Context, r *pb.PutRequest) (*pb.PutResponse, error) {
	return &pb.PutResponse{Header: &pb.ResponseHeader{Revision: 2}}, nil
}

// Range answers with one 5 MiB value: over grpc's default client receive limit (4 MiB).
func (bigKVServer) Range(_ context.Context, r *pb.RangeRequest) (*pb.RangeResponse, error) {
	return &pb.RangeResponse{
		Header: &pb.ResponseHeader{Revision: 2},
		Kvs:    []*mvccpb.KeyValue{{Key: r.Key, Value: make([]byte, 5<<20)}},
		Count:  1,
	}, nil
}

func ctxClientKV(t *testing.T, dialOpts ...grpc.DialOption) clientv3.KV {
	t.Helper()
	lis := bufconn.Listen(1 << 20)
	s := grpc.NewServer(grpc.MaxRecvMsgSize(bigServerLimit), grpc.MaxSendMsgSize(bigServerLimit))
	pb.RegisterKVServer(s, bigKVServer{})
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

// What the PR fixes: a response over 4 MiB. Fails at the base (grpc's default receive limit),
// passes at the PR head (defaultCallOpts' MaxCallRecvMsgSize(MaxInt32)).
func TestCtxClientLargeResponse(t *testing.T) {
	kv := ctxClientKV(t)
	_, err := kv.Get(context.Background(), "k")
	if err != nil {
		t.Fatalf("Get of a 5 MiB value: %v", err)
	}
}

// What the PR also changes: a request over 2 MiB. Passes at the base (grpc's default send limit
// is MaxInt32), fails at the PR head (defaultCallOpts' MaxCallSendMsgSize(2 MiB)).
func TestCtxClientLargeRequest(t *testing.T) {
	kv := ctxClientKV(t)
	_, err := kv.Put(context.Background(), "k", strings.Repeat("x", 3<<20))
	if err != nil {
		t.Fatalf("Put of a 3 MiB value: %v (code %v)", err, status.Code(err))
	}
}

// The same with the send limit raised on the caller's own connection: the PR's per-call
// option overrides the connection's default call option, so it still fails at the PR head. A
// NewCtxClient caller cannot change callOpts (unexported, and no Option sets it); only a client
// interceptor on its own connection, appending options after the per-call ones, can.
func TestCtxClientLargeRequestDialLimit(t *testing.T) {
	kv := ctxClientKV(t, grpc.WithDefaultCallOptions(grpc.MaxCallSendMsgSize(bigServerLimit)))
	_, err := kv.Put(context.Background(), "k", strings.Repeat("x", 3<<20))
	if err != nil {
		if status.Code(err) == codes.ResourceExhausted {
			t.Fatalf("Put of a 3 MiB value over a connection allowing 64 MiB: %v", err)
		}
		t.Fatal(err)
	}
}

// The third default: WaitForReady(true). With the server unreachable, a call fails at once with
// Unavailable at the base (grpc's default WaitForReady(false)); at the PR head it waits for the
// connection until the caller's deadline, DeadlineExceeded. (The client's retry interceptor,
// which retries Unavailable, is not on this caller-built connection.)
func TestCtxClientUnreachableFailsFast(t *testing.T) {
	lis := bufconn.Listen(1 << 20)
	lis.Close()
	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(ctx context.Context, _ string) (net.Conn, error) { return lis.DialContext(ctx) }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	defer conn.Close()
	c := clientv3.NewCtxClient(context.Background())
	defer c.Close()
	kv := clientv3.NewKVFromKVClient(pb.NewKVClient(conn), c)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	start := time.Now()
	_, err = kv.Put(ctx, "k", "v")
	t.Logf("Put: %v after %v", err, time.Since(start).Round(100*time.Millisecond))
	if status.Code(err) != codes.Unavailable {
		t.Fatalf("Put to an unreachable server: got code %v, want Unavailable (fail fast)", status.Code(err))
	}
}
