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

package clientv3

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// A fake gRPC watch stream; the test plays the server.
type nilRetcStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	recv chan nilRetcRecv
}

type nilRetcRecv struct {
	resp *pb.WatchResponse
	err  error
}

func (s *nilRetcStream) Send(r *pb.WatchRequest) error { s.sent <- r; return nil }

func (s *nilRetcStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

// Watch blocks until the test takes the new stream: the test holds run() in openWatchClient.
type nilRetcClient struct{ streams chan *nilRetcStream }

func (c *nilRetcClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &nilRetcStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), recv: make(chan nilRetcRecv, 16)}
	c.streams <- s
	return s, nil
}

// TestWatchResumeNilChannelOnRetc checks that run never sends a nil channel on a watch's retc:
// a watch whose create is in flight when the stream fails
// transiently, and whose context is canceled while run() reconnects, is closed by
// waitCancelSubstreams (outc closed and set to nil); closeSubstream then sends the nil outc on
// the watch's retc. Watch() returns what it receives on retc: if its goroutine reaches its
// receive after that send (it selects between retc and ctx.Done(), both ready), it returns a
// nil WatchChan, on which a receive blocks forever instead of seeing the channel closed. The
// test plays the late Watch() goroutine: it sends the request on reqc itself and reads retc.
func TestWatchResumeNilChannelOnRetc(t *testing.T) {
	fc := &nilRetcClient{streams: make(chan *nilRetcStream)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c).(*watcher)
	defer w.Close()
	// Watch B keeps the gRPC watch stream alive.
	chc := make(chan WatchChan, 1)
	go func() { chc <- w.Watch(context.Background(), "b") }()
	s1 := <-fc.streams
	<-s1.sent
	s1.recv <- nilRetcRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 0, Created: true}}
	<-chc

	// Watch A's request, as Watch() sends it.
	ctxA, cancelA := context.WithCancel(context.Background())
	defer cancelA()
	wr := &watchRequest{ctx: ctxA, key: "a", retc: make(chan chan WatchResponse, 1)}
	w.mu.Lock()
	wgs := w.streams[streamKeyFromCtx(ctxA)]
	w.mu.Unlock()
	wgs.reqc <- wr
	if r := <-s1.sent; string(r.GetCreateRequest().GetKey()) != "a" {
		t.Fatalf("unexpected request %v", r)
	}
	// The stream fails before A is created; run() reconnects and waits in openWatchClient
	// (Watch blocks until the test takes the stream) while A's context is canceled.
	s1.recv <- nilRetcRecv{err: status.Error(codes.Unavailable, "transient")}
	time.Sleep(50 * time.Millisecond)
	cancelA()
	time.Sleep(50 * time.Millisecond)
	<-fc.streams
	select {
	case ch := <-wr.retc:
		if ch == nil {
			t.Fatal("retc carries a nil WatchChan: Watch() may return a channel that never closes")
		}
		select {
		case _, ok := <-ch:
			if ok {
				t.Fatal("A's channel delivered a response")
			}
		case <-time.After(time.Second):
			t.Fatal("A's channel is not closed")
		}
	case <-time.After(time.Second):
		// nothing on retc: Watch() reports the canceled context with its own closed channel
	}
}
