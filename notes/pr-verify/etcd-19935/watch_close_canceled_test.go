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

	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// closeTestStream is a fake gRPC watch stream whose Recv fails with the stream context's
// error once that context is canceled, as a real gRPC client stream does.
type closeTestStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	recv chan *pb.WatchResponse
}

func (s *closeTestStream) Send(r *pb.WatchRequest) error {
	select {
	case s.sent <- r:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *closeTestStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r, nil
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type closeTestWatchClient struct{ streams chan *closeTestStream }

func (c *closeTestWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &closeTestStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), recv: make(chan *pb.WatchResponse, 16)}
	c.streams <- s
	return s, nil
}

// TestWatcherCloseIgnoresCanceled checks that closing a watcher with an open watch stream
// returns nil: the stream's close reports context.Canceled, which Close treats as a
// successful close.
func TestWatcherCloseIgnoresCanceled(t *testing.T) {
	for i := 0; i < 2000; i++ {
		fc := &closeTestWatchClient{streams: make(chan *closeTestStream, 1)}
		w := NewWatchFromWatchClient(fc, nil)

		chc := make(chan WatchChan, 1)
		go func() { chc <- w.Watch(context.Background(), "a", WithCreatedNotify()) }()
		s := <-fc.streams
		if r := <-s.sent; r.GetCreateRequest() == nil {
			t.Fatalf("expected a create request, got %v", r)
		}
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 1, Created: true}
		wch := <-chc
		if resp := <-wch; !resp.Created {
			t.Fatalf("expected the created notification, got %v", resp)
		}
		if err := w.Close(); err != nil {
			t.Fatalf("iteration %d: Close() = %v, want nil", i, err)
		}
	}
}
