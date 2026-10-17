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

// Probe for etcd-io/etcd#21684: what a lease keep-alive client sees, over a real gRPC
// connection, when the server's LeaseRenew fails with lease.ErrNotPrimary (the
// `!s.ensureLeadership()` branch of EtcdServer.LeaseRenew), and what clientv3's
// KeepAliveOnce does with it. Goes in server/etcdserver/api/v3rpc/.

import (
	"context"
	"errors"
	"net"
	"sync/atomic"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"
	"google.golang.org/grpc/test/bufconn"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/lease"
)

type notPrimaryLessor struct{ renews atomic.Int64 }

func (*notPrimaryLessor) LeaseGrant(context.Context, *pb.LeaseGrantRequest) (*pb.LeaseGrantResponse, error) {
	return nil, errors.New("unused")
}

func (*notPrimaryLessor) LeaseRevoke(context.Context, *pb.LeaseRevokeRequest) (*pb.LeaseRevokeResponse, error) {
	return nil, errors.New("unused")
}

func (l *notPrimaryLessor) LeaseRenew(context.Context, lease.LeaseID) (int64, error) {
	l.renews.Add(1)
	return -1, lease.ErrNotPrimary
}

func (*notPrimaryLessor) LeaseTimeToLive(context.Context, *pb.LeaseTimeToLiveRequest) (*pb.LeaseTimeToLiveResponse, error) {
	return nil, errors.New("unused")
}

func (*notPrimaryLessor) LeaseLeases(context.Context, *pb.LeaseLeasesRequest) (*pb.LeaseLeasesResponse, error) {
	return nil, errors.New("unused")
}

type probeStatusGetter struct{}

func (probeStatusGetter) MemberID() types.ID     { return 1 }
func (probeStatusGetter) Leader() types.ID       { return 1 }
func (probeStatusGetter) CommittedIndex() uint64 { return 0 }
func (probeStatusGetter) AppliedIndex() uint64   { return 0 }
func (probeStatusGetter) Term() uint64           { return 1 }

func startNotPrimaryLeaseServer(t *testing.T) (pb.LeaseClient, *notPrimaryLessor) {
	le := &notPrimaryLessor{}
	ls := &LeaseServer{lg: zap.NewNop(), le: le, hdr: header{clusterID: 1, memberID: 1,
		sg: probeStatusGetter{}, rev: func() int64 { return 1 }}}
	lis := bufconn.Listen(1 << 20)
	srv := grpc.NewServer()
	pb.RegisterLeaseServer(srv, ls)
	go srv.Serve(lis)
	t.Cleanup(srv.Stop)
	conn, err := grpc.NewClient("passthrough:///bufnet",
		grpc.WithContextDialer(func(context.Context, string) (net.Conn, error) { return lis.Dial() }),
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { conn.Close() })
	return pb.NewLeaseClient(conn), le
}

// The code the keep-alive stream ends with, and the client-side error rpctypes.Error makes of it.
func TestProbeLeaseKeepAliveNotPrimaryCode(t *testing.T) {
	lc, _ := startNotPrimaryLeaseServer(t)
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	stream, err := lc.LeaseKeepAlive(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if err := stream.Send(&pb.LeaseKeepAliveRequest{ID: 7}); err != nil {
		t.Fatal(err)
	}
	_, err = stream.Recv()
	t.Logf("server error: code=%v err=%v", status.Code(err), err)
	var ee rpctypes.EtcdError
	t.Logf("rpctypes.Error: %v (an EtcdError: %v)", rpctypes.Error(err), errors.As(rpctypes.Error(err), &ee))
	if status.Code(err) != codes.Unavailable {
		t.Errorf("expected codes.Unavailable, got %v", status.Code(err))
	}
}

// The same through a full clientv3.Client (clientv3.New, with its retry interceptors) over TCP.
func TestProbeClientKeepAliveOnceNotPrimary(t *testing.T) {
	le := &notPrimaryLessor{}
	ls := &LeaseServer{lg: zap.NewNop(), le: le, hdr: header{clusterID: 1, memberID: 1,
		sg: probeStatusGetter{}, rev: func() int64 { return 1 }}}
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	srv := grpc.NewServer()
	pb.RegisterLeaseServer(srv, ls)
	go srv.Serve(lis)
	defer srv.Stop()
	c, err := clientv3.New(clientv3.Config{Endpoints: []string{lis.Addr().String()}, DialTimeout: time.Second,
		Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 300*time.Millisecond)
	defer cancel()
	start := time.Now()
	_, err = c.KeepAliveOnce(ctx, 7)
	var ee rpctypes.EtcdError
	isEE := errors.As(err, &ee)
	t.Logf("clientv3 KeepAliveOnce: err=%v (EtcdError: %v, EtcdError.Code: %v, status.Code: %v) after %v, server renews=%d",
		err, isEE, ee.Code(), status.Code(err), time.Since(start), le.renews.Load())
}

// clientv3's KeepAliveOnce over a bare connection (NewLeaseFromLeaseClient): does it retry (its
// loop retries while isHaltErr is false)? Counts the server's renew calls in 300ms. It fails, at
// the PR head as before it: KeepAliveOnce calls isHaltErr on ContextError's result, which for an
// error rpctypes knows is an EtcdError, whose status.Code is Unknown.
func TestProbeKeepAliveOnceNotPrimary(t *testing.T) {
	lc, le := startNotPrimaryLeaseServer(t)
	c := clientv3.NewCtxClient(context.Background())
	defer c.Close()
	l := clientv3.NewLeaseFromLeaseClient(lc, c, time.Second)
	defer l.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 300*time.Millisecond)
	defer cancel()
	start := time.Now()
	_, err := l.KeepAliveOnce(ctx, 7)
	t.Logf("KeepAliveOnce: err=%v after %v, server renews=%d", err, time.Since(start), le.renews.Load())
	if le.renews.Load() < 2 {
		t.Errorf("expected KeepAliveOnce to retry, got %d renew(s)", le.renews.Load())
	}
}
