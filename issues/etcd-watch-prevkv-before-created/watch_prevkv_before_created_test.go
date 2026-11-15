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

package watch

import (
	"context"
	"fmt"
	"sync"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3WatchPrevKVBeforeCreated ensures that every event of a PrevKv watch on
// a key written before the watch carries the previous key-value, including the
// events mvcc queues for the watcher before recvLoop records its PrevKv option.
// Sixteen streams create such watches on a key under concurrent puts; run with
// GOMAXPROCS=2 or 4 (the race needs recvLoop to yield between mvcc's Watch and
// sws.mu.Lock).
func TestV3WatchPrevKVBeforeCreated(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	ctx, cancel := context.WithTimeout(t.Context(), 120*time.Second)
	defer cancel()
	kvc := integration.ToGRPC(clus.RandClient()).KV
	if _, err := kvc.Put(ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte("v")}); err != nil {
		t.Fatal(err)
	}
	stop := make(chan struct{})
	var wg sync.WaitGroup
	for i := 0; i < 8; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				kvc.Put(ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte("v")})
			}
		}()
	}
	defer func() { close(stop); wg.Wait() }()

	errc := make(chan error, 64)
	var cw sync.WaitGroup
	for c := 0; c < 16; c++ {
		cw.Add(1)
		go func() {
			defer cw.Done()
			for iter := 0; iter < 1500; iter++ {
				ictx, icancel := context.WithCancel(ctx)
				ws, err := integration.ToGRPC(clus.RandClient()).Watch.Watch(ictx)
				if err != nil {
					errc <- err
					return
				}
				if err := ws.Send(&pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
					CreateRequest: &pb.WatchCreateRequest{Key: []byte("k"), PrevKv: true},
				}}); err != nil {
					errc <- err
					return
				}
				got := 0
				for got < 3 {
					r, err := ws.Recv()
					if err != nil {
						errc <- err
						return
					}
					for _, ev := range r.Events {
						got++
						if ev.PrevKv == nil {
							errc <- fmt.Errorf("iteration %d: event at revision %d (version %d) of a PrevKv watch without PrevKv",
								iter, ev.Kv.ModRevision, ev.Kv.Version)
							return
						}
					}
				}
				icancel()
			}

		}()
	}
	cw.Wait()
	close(errc)
	for err := range errc {
		t.Fatal(err)
	}
}
