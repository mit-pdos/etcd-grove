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
	"go.etcd.io/etcd/api/v3/mvccpb"
)

type reconnRecv struct {
	resp *pb.WatchResponse
	err  error
}

// reconnStream is a fake gRPC watch stream: the test plays the server.
type reconnStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	recv chan reconnRecv
	slow bool // every Send is slow
}

func (s *reconnStream) Send(r *pb.WatchRequest) error {
	if s.slow || r.GetCancelRequest() != nil {
		// a slow send: run() is busy while two of its select's cases become ready
		// (the stream's error or a response, and A's closingc), so it picks either
		time.Sleep(5 * time.Millisecond)
	}
	select {
	case s.sent <- r:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *reconnStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

// reconnWatchClient opens fake streams; the n-th stream (from 0) starts with the responses
// prefill[n] already queued, as a server that answers before the test looks.
type reconnWatchClient struct {
	streams chan *reconnStream
	n       int
	prefill [][]reconnRecv
}

func (c *reconnWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &reconnStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), recv: make(chan reconnRecv, 16)}
	s.slow = c.n > 0
	if c.n < len(c.prefill) {
		for _, r := range c.prefill[c.n] {
			s.recv <- r
		}
	}
	c.n++
	c.streams <- s
	return s, nil
}

func reconnCreate(t *testing.T, s *reconnStream) {
	t.Helper()
	select {
	case r := <-s.sent:
		if r.GetCreateRequest() == nil {
			t.Fatalf("expected a create request, got %v", r)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("no create request")
	}
}

// TestWatchServerCancelThenReconnectKeepsOtherWatch: the server cancels watch A (id 0) and the
// stream then fails with a retryable error. The client reconnects and resumes watch B, which
// the new stream (whose ids start again at 0) creates with id 0. When run() takes A from
// closingc after B's Created, closeSubstream(A) deletes substreams[A.id] = substreams[0], which
// is now B: B's events are dropped (and, B being the last watch, run returns and never closes
// B's channel). B must still receive its events.
func TestWatchServerCancelThenReconnectKeepsOtherWatch(t *testing.T) {
	lost, hung := 0, 0
	const trials = 200
	for i := 0; i < trials; i++ {
		hdr := &pb.ResponseHeader{Revision: 1}
		ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("b"), ModRevision: 2}}
		// The second stream answers B's resume at once: Created with id 0 (a new stream's
		// ids start again at 0), then an event for it.
		fc := &reconnWatchClient{streams: make(chan *reconnStream, 2), prefill: [][]reconnRecv{nil, {
			{resp: &pb.WatchResponse{Header: hdr, WatchId: 0, Created: true}},
			{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 0, Events: []*mvccpb.Event{ev}}},
		}}}
		c := &Client{}
		c.lg.Store(zap.NewNop())
		w := NewWatchFromWatchClient(fc, c)

		cha := make(chan WatchChan, 1)
		go func() { cha <- w.Watch(context.Background(), "a", WithCreatedNotify()) }()
		s1 := <-fc.streams
		reconnCreate(t, s1)
		s1.recv <- reconnRecv{resp: &pb.WatchResponse{Header: hdr, WatchId: 0, Created: true}}
		wa := <-cha
		<-wa

		chb := make(chan WatchChan, 1)
		go func() { chb <- w.Watch(context.Background(), "b", WithCreatedNotify()) }()
		reconnCreate(t, s1)
		s1.recv <- reconnRecv{resp: &pb.WatchResponse{Header: hdr, WatchId: 1, Created: true}}
		wb := <-chb
		<-wb

		// The server cancels A, sends an event for an id the client does not know (run()
		// answers it with a cancel request), then the stream fails (retryable).
		s1.recv <- reconnRecv{resp: &pb.WatchResponse{Header: hdr, WatchId: 0, Canceled: true}}
		s1.recv <- reconnRecv{resp: &pb.WatchResponse{Header: hdr, WatchId: 7, Events: []*mvccpb.Event{ev}}}
		s1.recv <- reconnRecv{err: status.Error(codes.Unavailable, "transient")}

		s2 := <-fc.streams
		reconnCreate(t, s2) // B's resume

		got := false
		timeout := time.After(time.Second)
	loop:
		for {
			select {
			case resp, ok := <-wb:
				if !ok {
					break loop
				}
				if len(resp.Events) > 0 {
					got = true
					break loop
				}
			case <-timeout:
				break loop
			}
		}
		if !got {
			lost++
		}
		closed := make(chan struct{})
		go func() { w.Close(); close(closed) }()
		select {
		case <-closed:
		case <-time.After(5 * time.Second):
			hung++ // the goroutines stay blocked; go on with a fresh watcher
		}
	}
	if lost > 0 || hung > 0 {
		t.Fatalf("of %d trials: watch B lost its event in %d, Close() hung in %d", trials, lost, hung)
	}
}
