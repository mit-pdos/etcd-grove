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
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

// An etcd-like fake watch stream: per-stream watch ids from 0 (mvcc's nextID), a Created
// response for every create, a Canceled response only in answer to a cancel request for an
// existing id (v3rpc recvLoop), nothing for an unknown id. Sends are slow (run() busy).
// failAfterCancel: after answering the first cancel request, the stream fails (Unavailable).
type elStream struct {
	grpc.ClientStream
	ctx             context.Context
	recv            chan reconnRecv
	mu              sync.Mutex
	nextID          int64
	byKey           map[string]int64
	failAfterCancel bool
	failed          bool
}

func (s *elStream) Send(r *pb.WatchRequest) error {
	s.mu.Lock()
	switch {
	case r.GetCreateRequest() != nil:
		id := s.nextID
		s.nextID++
		s.byKey[string(r.GetCreateRequest().Key)] = id
		s.recv <- reconnRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: id, Created: true}}
	case r.GetCancelRequest() != nil:
		id := r.GetCancelRequest().WatchId
		for k, v := range s.byKey {
			if v == id {
				delete(s.byKey, k)
				s.recv <- reconnRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: id, Canceled: true}}
				if s.failAfterCancel && !s.failed {
					s.failed = true
					s.recv <- reconnRecv{err: status.Error(codes.Unavailable, "transient")}
				}
			}
		}
	}
	s.mu.Unlock()
	time.Sleep(3 * time.Millisecond)
	return nil
}

func (s *elStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

func (s *elStream) idOf(key string) (int64, bool) {
	s.mu.Lock()
	defer s.mu.Unlock()
	id, ok := s.byKey[key]
	return id, ok
}

type elClient struct {
	streams chan *elStream
	n       int
}

func (c *elClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &elStream{ctx: ctx, recv: make(chan reconnRecv, 64), byKey: map[string]int64{}, failAfterCancel: c.n == 0}
	c.n++
	c.streams <- s
	return s, nil
}

// The user cancels watch A (id 0) while an event for it is in flight; run() cannot dispatch
// it and sends a cancel request; etcd answers Canceled (run removes A from substreams, A's id
// left at 0); the stream then fails with Unavailable. B is resumed on the new stream and gets
// id 0. B must keep receiving its events and Close() must return.
func TestWatchStaleIDEtcdLike(t *testing.T) {
	const trials = 300
	var got, silentClose, lost, hung, reached int
	for i := 0; i < trials; i++ {
		fc := &elClient{streams: make(chan *elStream, 4)}
		c := &Client{}
		c.lg.Store(zap.NewNop())
		w := NewWatchFromWatchClient(fc, c)

		actx, acancel := context.WithCancel(context.Background())
		wa := w.Watch(actx, "a", WithCreatedNotify())
		<-wa
		s1 := <-fc.streams
		wb := w.Watch(context.Background(), "b", WithCreatedNotify())
		<-wb

		// make run() busy in a (slow) progress-request Send, cancel A, queue an event for A
		go w.RequestProgress(context.Background())
		time.Sleep(time.Millisecond)
		acancel()
		ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("a"), ModRevision: 2}}
		s1.recv <- reconnRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 0, Events: []*mvccpb.Event{ev}}}
		// other client activity (progress requests) keeps run() busy in Sends meanwhile
		for j := 0; j < 3; j++ {
			go w.RequestProgress(context.Background())
		}

		var s2 *elStream
		select {
		case s2 = <-fc.streams:
		case <-time.After(200 * time.Millisecond):
		}
		if s2 != nil {
			reached++
			time.Sleep(20 * time.Millisecond)
			if id, ok := s2.idOf("b"); ok {
				evb := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("b"), ModRevision: 3}}
				s2.recv <- reconnRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 3}, WatchId: id, Events: []*mvccpb.Event{evb}}}
			}
			timeout := time.After(time.Second)
			res := 0
		loop:
			for {
				select {
				case r, ok := <-wb:
					if !ok {
						res = 1
						break loop
					}
					if len(r.Events) > 0 {
						res = 2
						break loop
					}
				case <-timeout:
					break loop
				}
			}
			switch res {
			case 0:
				lost++
			case 1:
				silentClose++
			case 2:
				got++
			}
		}
		closed := make(chan struct{})
		go func() { w.Close(); close(closed) }()
		select {
		case <-closed:
		case <-time.After(3 * time.Second):
			hung++
		}
	}
	t.Logf("trials %d, reconnect reached %d: B got event %d, B channel closed silently %d, B event lost (open) %d; Close hung %d",
		trials, reached, got, silentClose, lost, hung)
	if lost+silentClose+hung > 0 {
		t.Fail()
	}
}
