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

import (
	"context"
	"errors"
	"io"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"
	"google.golang.org/grpc"
	"google.golang.org/grpc/metadata"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// idleRawStream is a grpc.ServerStream whose RecvMsg, like grpc's, waits for the
// next message from the client or for the end of the RPC (its own context), and
// does not watch any context a stream interceptor wraps it with.
type idleRawStream struct {
	ctx  context.Context
	msgs chan *pb.LeaseKeepAliveRequest
}

func (s *idleRawStream) SetHeader(metadata.MD) error  { return nil }
func (s *idleRawStream) SendHeader(metadata.MD) error { return nil }
func (s *idleRawStream) SetTrailer(metadata.MD)       {}
func (s *idleRawStream) Context() context.Context     { return s.ctx }
func (s *idleRawStream) SendMsg(any) error            { return nil }
func (s *idleRawStream) RecvMsg(m any) error {
	select {
	case req, ok := <-s.msgs:
		if !ok {
			return io.EOF
		}
		*(m.(*pb.LeaseKeepAliveRequest)) = *req
		return nil
	case <-s.ctx.Done():
		return s.ctx.Err()
	}
}

// TestLeaseKeepAliveReturnsOnNoLeader: a keep-alive stream of a client that
// requires a leader (`WithRequireLeader`) is wrapped by the stream interceptor in a
// serverStreamWithCtx whose context monitorLeader cancels with ErrGRPCNoLeader once
// the member has had no leader for a while. LeaseKeepAlive must then end the RPC
// with that error, while the client is idle (no keep-alive request in flight), as
// the comment of the select it had said ("Server cancellation: ... monitorLeader()
// detects no leader and thus cancels this stream with ErrGRPCNoLeader").
func TestLeaseKeepAliveReturnsOnNoLeader(t *testing.T) {
	rpcCtx, rpcCancel := context.WithCancel(context.Background())
	defer rpcCancel()
	raw := &idleRawStream{ctx: rpcCtx, msgs: make(chan *pb.LeaseKeepAliveRequest)}

	// What newStreamInterceptor does for a require-leader stream.
	cctx := newCancellableContext(raw.Context())
	var ss grpc.ServerStream = serverStreamWithCtx{ctx: cctx, ServerStream: raw}
	stream := &grpc.GenericServerStream[pb.LeaseKeepAliveRequest, pb.LeaseKeepAliveResponse]{ServerStream: ss}

	ls := &LeaseServer{lg: zaptest.NewLogger(t)}
	done := make(chan error, 1)
	go func() { done <- ls.LeaseKeepAlive(stream) }()

	// What monitorLeader does after maxNoLeaderCnt election timeouts with no leader.
	time.Sleep(50 * time.Millisecond)
	cctx.Cancel(rpctypes.ErrGRPCNoLeader)

	select {
	case err := <-done:
		if !errors.Is(err, rpctypes.ErrGRPCNoLeader) {
			t.Fatalf("LeaseKeepAlive returned %v, want %v", err, rpctypes.ErrGRPCNoLeader)
		}
	case <-time.After(3 * time.Second):
		t.Fatal("LeaseKeepAlive did not return after the stream's context was canceled with ErrGRPCNoLeader")
	}
}
