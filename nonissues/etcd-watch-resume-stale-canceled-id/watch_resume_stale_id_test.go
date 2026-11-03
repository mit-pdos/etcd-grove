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
	"errors"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

// A fake gRPC watch stream; the test plays the server. Send blocks until the test opens the
// gate, so that the test can make run() busy while it readies two of its select's cases.
type staleWatchStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	gate chan struct{}
	recv chan staleRecv
}

type staleRecv struct {
	resp *pb.WatchResponse
	err  error
}

func (s *staleWatchStream) Send(r *pb.WatchRequest) error {
	s.sent <- r
	select {
	case <-s.gate:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *staleWatchStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type staleWatchClient struct{ streams chan *staleWatchStream }

func (c *staleWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &staleWatchStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16),
		gate: make(chan struct{}, 16), recv: make(chan staleRecv, 16)}
	c.streams <- s
	return s, nil
}

var errStaleLost = errors.New("interleaving not hit")

func staleSent(s *staleWatchStream) (*pb.WatchRequest, error) {
	select {
	case r := <-s.sent:
		return r, nil
	case <-time.After(100 * time.Millisecond):
		return nil, errStaleLost
	}
}

const staleSettle = 3 * time.Millisecond

func staleCreate(s *staleWatchStream, id int64) error {
	if _, err := staleSent(s); err != nil {
		return err
	}
	s.recv <- staleRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: id, Created: true}}
	s.gate <- struct{}{}
	return nil
}

// One trial: watch A (id 0) and watch B (id 1) on stream s1. A's context is canceled and an
// event for A arrives; run cannot dispatch it, sends a cancel request, and the server answers
// with a Canceled response, on which run closes A's recvc and drops A from substreams (keeping
// its id 0). The stream then fails transiently; run reconnects (s2) and resumes B, which the
// server registers as id 0 on s2. If run takes A from closingc only now, closeSubstream deletes
// substreams[0]: B. Returns errStaleLost if B still gets its event on s2.
func staleTrial() (int, error) {
	fc := &staleWatchClient{streams: make(chan *staleWatchStream, 4)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c)
	defer func() {
		done := make(chan struct{})
		go func() { w.Close(); close(done) }()
		select {
		case <-done:
		case <-time.After(time.Second):
		}
	}()
	ctxA, cancelA := context.WithCancel(context.Background())
	defer cancelA()
	chc := make(chan WatchChan, 1)
	go func() { chc <- w.Watch(ctxA, "a") }()
	s1 := <-fc.streams
	if err := staleCreate(s1, 0); err != nil {
		return 0, err
	}
	<-chc
	go func() { chc <- w.Watch(context.Background(), "b") }()
	if err := staleCreate(s1, 1); err != nil {
		return 0, err
	}
	chB := <-chc
	// Make run() busy in a Send (a progress request), then cancel A's context (its substream
	// goroutine exits, closing, and waits on closingc) and queue an event for A.
	go w.RequestProgress(context.Background())
	if _, err := staleSent(s1); err != nil {
		return 1, err
	}
	cancelA()
	ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("a"), ModRevision: 2}}
	s1.recv <- staleRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 0, Events: []*mvccpb.Event{ev}}}
	time.Sleep(staleSettle)
	s1.gate <- struct{}{}
	r, err := staleSent(s1)
	if err != nil || r.GetCancelRequest() == nil {
		return 2, errStaleLost
	}
	// The server answers the cancel (as etcd's does), then the stream fails transiently.
	s1.recv <- staleRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 0, Canceled: true}}
	s1.recv <- staleRecv{err: status.Error(codes.Unavailable, "transient")}
	go w.RequestProgress(context.Background())
	time.Sleep(staleSettle)
	s1.gate <- struct{}{}
	if r, err := staleSent(s1); err != nil || r.GetProgressRequest() == nil {
		return 3, errStaleLost
	}
	time.Sleep(staleSettle)
	s1.gate <- struct{}{}
	var s2 *staleWatchStream
	select {
	case s2 = <-fc.streams:
	case <-time.After(100 * time.Millisecond):
		return 4, errStaleLost
	}
	r, err = staleSent(s2) // the resumed create request
	if err != nil {
		return 5, err
	}
	if k := string(r.GetCreateRequest().GetKey()); k != "b" {
		return 5, errors.New("resumed " + k)
	}
	s2.recv <- staleRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 0, Created: true}}
	time.Sleep(staleSettle)
	s2.gate <- struct{}{}
	time.Sleep(staleSettle)
	// An event for B (id 0 on s2): B must receive it.
	evB := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("b"), ModRevision: 3}}
	s2.recv <- staleRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 3}, WatchId: 0, Events: []*mvccpb.Event{evB}}}
	for {
		select {
		case resp, ok := <-chB:
			if !ok {
				return 6, errors.New("B's channel closed")
			}
			if len(resp.Events) > 0 {
				return 6, errStaleLost
			}
		case <-time.After(time.Second):
			return 7, nil
		}
	}
}

// TestWatchResumeStaleCanceledID checks that a watch the server canceled does not, once run
// takes it from closingc after a reconnect, delete the resumed watch the new stream registered
// under the same id: without the fix, some trial hits the interleaving above and the resumed
// watch never gets its event (run stops: it finds no substream left).
func TestWatchResumeStaleCanceledID(t *testing.T) {
	var stages [8]int
	for i := 0; i < 300; i++ {
		st, err := staleTrial()
		stages[st]++
		if err == nil {
			t.Fatalf("trial %d: the resumed watch lost its event (run deleted it under the canceled watch's stale id); trials lost at each stage: %v", i, stages)
		}
		if err != errStaleLost {
			t.Fatal(err)
		}
	}
	t.Logf("not hit; trials lost at each stage: %v", stages)
}
