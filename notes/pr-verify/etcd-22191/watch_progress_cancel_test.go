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

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// cancelTestStream is a fake gRPC watch stream: the test plays the server.
type cancelTestStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	recv chan *pb.WatchResponse
}

func (s *cancelTestStream) Send(r *pb.WatchRequest) error {
	select {
	case s.sent <- r:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *cancelTestStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r, nil
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type cancelTestWatchClient struct{ streams chan *cancelTestStream }

func (c *cancelTestWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &cancelTestStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), recv: make(chan *pb.WatchResponse, 16)}
	c.streams <- s
	return s, nil
}

// TestWatchProgressBroadcastAfterServerCancel checks that a progress notification broadcast
// (watch id -1) that follows the server's cancellation of a watch is not sent on the canceled
// substream's closed channel, which panicked with "send on closed channel".
func TestWatchProgressBroadcastAfterServerCancel(t *testing.T) {
	for i := 0; i < 200; i++ {
		fc := &cancelTestWatchClient{streams: make(chan *cancelTestStream, 1)}
		c := &Client{}
		c.lg.Store(zap.NewNop())
		w := NewWatchFromWatchClient(fc, c)

		chc := make(chan WatchChan, 1)
		go func() { chc <- w.Watch(context.Background(), "a", WithCreatedNotify()) }()
		s := <-fc.streams
		if r := <-s.sent; r.GetCreateRequest() == nil {
			t.Fatalf("expected a create request, got %v", r)
		}
		hdr := &pb.ResponseHeader{Revision: 1}
		s.recv <- &pb.WatchResponse{Header: hdr, WatchId: 1, Created: true}
		wch := <-chc
		if resp := <-wch; !resp.Created {
			t.Fatalf("expected the created notification, got %v", resp)
		}

		// The server cancels the watch, then answers a progress request of the stream.
		s.recv <- &pb.WatchResponse{Header: hdr, WatchId: 1, Canceled: true}
		s.recv <- &pb.WatchResponse{Header: hdr, WatchId: InvalidWatchID}

		select {
		case _, ok := <-wch:
			for ok {
				_, ok = <-wch
			}
		case <-time.After(5 * time.Second):
			t.Fatal("the canceled watch's channel was not closed")
		}
		if err := w.Close(); err != nil {
			t.Fatal(err)
		}
	}
}
