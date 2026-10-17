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

package v3rpc

// Review tests for etcd-io/etcd#21960, over a real grpc server and client on a
// loopback TCP connection (no mock stream).

import (
	"context"
	"errors"
	"net"
	"runtime"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/lease"
)

type rvLessor struct{ etcdserver.Lessor }

func (rvLessor) LeaseRenew(ctx context.Context, id lease.LeaseID) (int64, error) { return 10, nil }

type rvSG struct{ apply.RaftStatusGetter }

func (rvSG) Term() uint64      { return 1 }
func (rvSG) Leader() types.ID { return 1 }

type rvServer struct {
	addr     string
	gs       *grpc.Server
	cancels  chan *cancellableContext // the require-leader wrapper's context, per stream
	handlerc chan error               // the handler's return, per stream
}

// startServer serves the LeaseServer; with wrap, its stream interceptor does
// what newStreamInterceptor does for a WithRequireLeader stream.
func startServer(t *testing.T, wrap bool) *rvServer {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := &rvServer{addr: lis.Addr().String(), cancels: make(chan *cancellableContext, 4), handlerc: make(chan error, 4)}
	icpt := func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo, handler grpc.StreamHandler) error {
		if wrap {
			ctx := newCancellableContext(ss.Context())
			ss = serverStreamWithCtx{ctx: ctx, ServerStream: ss}
			s.cancels <- ctx
			defer ctx.Cancel(nil)
		}
		err := handler(srv, ss)
		s.handlerc <- err
		return err
	}
	s.gs = grpc.NewServer(grpc.StreamInterceptor(icpt))
	ls := &LeaseServer{lg: zaptest.NewLogger(t), le: rvLessor{}, hdr: header{sg: rvSG{}, rev: func() int64 { return 1 }}}
	pb.RegisterLeaseServer(s.gs, ls)
	go s.gs.Serve(lis)
	t.Cleanup(s.gs.Stop)
	return s
}

func dial(t *testing.T, addr string, opts ...grpc.DialOption) pb.LeaseClient {
	opts = append(opts, grpc.WithTransportCredentials(insecure.NewCredentials()))
	conn, err := grpc.NewClient(addr, opts...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return pb.NewLeaseClient(conn)
}

// loopGoroutines counts the goroutines running leaseKeepAlive.
func loopGoroutines() int {
	buf := make([]byte, 1<<22)
	buf = buf[:runtime.Stack(buf, true)]
	n := 0
	for _, g := range strings.Split(string(buf), "\n\n") {
		if strings.Contains(g, "v3rpc.(*LeaseServer).leaseKeepAlive(") {
			n++
		}
	}
	return n
}

func waitNoLoop(t *testing.T) {
	deadline := time.Now().Add(3 * time.Second)
	for loopGoroutines() > 0 {
		if time.Now().After(deadline) {
			t.Fatalf("a leaseKeepAlive goroutine is still running 3s after the handler returned")
		}
		time.Sleep(10 * time.Millisecond)
	}
}

func waitHandler(t *testing.T, s *rvServer, what string) error {
	select {
	case err := <-s.handlerc:
		return err
	case <-time.After(3 * time.Second):
		t.Fatalf("%s: LeaseKeepAlive did not return within 3s", what)
		return nil
	}
}

// F2: the client cancels; the handler returns and (old code) the loop goroutine,
// blocked in Recv, exits too: grpc cancels the stream when the handler returns.
func TestReviewClientCancelNoLeak(t *testing.T) {
	s := startServer(t, false)
	c := dial(t, s.addr)
	ctx, cancel := context.WithCancel(context.Background())
	st, err := c.LeaseKeepAlive(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if err := st.Send(&pb.LeaseKeepAliveRequest{ID: 1}); err != nil {
		t.Fatal(err)
	}
	if _, err := st.Recv(); err != nil {
		t.Fatal(err)
	}
	cancel()
	t.Logf("handler returned %v", waitHandler(t, s, "client cancel"))
	waitNoLoop(t)
}

// F2 and F1: the require-leader wrapper's context is canceled with
// ErrGRPCNoLeader (monitorLeader) while the client is idle. The client must get
// ErrGRPCNoLeader; (old code) the loop goroutine then exits.
func TestReviewNoLeaderIdle(t *testing.T) {
	s := startServer(t, true)
	c := dial(t, s.addr)
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	st, err := c.LeaseKeepAlive(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if err := st.Send(&pb.LeaseKeepAliveRequest{ID: 1}); err != nil {
		t.Fatal(err)
	}
	if _, err := st.Recv(); err != nil {
		t.Fatal(err)
	}
	(<-s.cancels).Cancel(rpctypes.ErrGRPCNoLeader)
	herr := waitHandler(t, s, "no leader, client idle")
	t.Logf("handler returned %v", herr)
	_, err = st.Recv()
	if !errors.Is(err, rpctypes.ErrGRPCNoLeader) && rpctypes.ErrorDesc(err) != rpctypes.ErrorDesc(rpctypes.ErrGRPCNoLeader) {
		t.Fatalf("client got %v, want %v", err, rpctypes.ErrGRPCNoLeader)
	}
	waitNoLoop(t)
}

// F1, Send side: the client does not read its responses, so the server's Send
// blocks on flow control; then the wrapper's context is canceled with
// ErrGRPCNoLeader. The handler must return; (old code) the loop goroutine,
// blocked in Send, exits too.
func TestReviewNoLeaderSendBlocked(t *testing.T) {
	s := startServer(t, true)
	// A fixed window (no BDP growth), so that the server's sends block.
	c := dial(t, s.addr, grpc.WithInitialWindowSize(1<<16), grpc.WithInitialConnWindowSize(1<<16))
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	st, err := c.LeaseKeepAlive(ctx)
	if err != nil {
		t.Fatal(err)
	}
	go func() {
		for i := 0; i < 200000; i++ {
			if st.Send(&pb.LeaseKeepAliveRequest{ID: int64(i + 1)}) != nil {
				return
			}
		}
	}()
	time.Sleep(1 * time.Second) // the server's Send is blocked by now
	if loopGoroutines() != 1 {
		t.Fatalf("expected the loop to be running (blocked), found %d", loopGoroutines())
	}
	(<-s.cancels).Cancel(rpctypes.ErrGRPCNoLeader)
	t.Logf("handler returned %v", waitHandler(t, s, "no leader, Send blocked"))
	waitNoLoop(t)
}
