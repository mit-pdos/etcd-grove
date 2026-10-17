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


// A stress probe written by the reviewer of the verification of etcd-io/etcd#22185.

package mvcc

import (
	"context"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Probe: concurrent writers, Commit, Compact-free Restore-free progress requests and
// watch creation; checks no deadlock (deadline), no data race (-race), and that every progress
// response's revision is >= every event revision previously delivered on the same channel and
// that events after it are > it (progress consistent with notified events).
func TestReviewProgressIfSyncStress(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}).(*watchableStore)
	defer s.Close()

	ws := s.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.Background(), 0, []byte("k"), []byte("l"), 0)
	if err != nil {
		t.Fatal(err)
	}

	stop := make(chan struct{})
	var wg sync.WaitGroup
	for g := 0; g < 2; g++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				tw := s.Write(traceutil.TODO())
				tw.Put([]byte("k1"), []byte("v"), lease.NoLease)
				tw.End()
			}
		}()
	}
	wg.Add(2)
	go func() {
		defer wg.Done()
		for {
			select {
			case <-stop:
				return
			default:
			}
			s.Commit()
		}
	}()
	go func() {
		defer wg.Done()
		for {
			select {
			case <-stop:
				return
			default:
			}
			ws.RequestProgress(id)
			time.Sleep(50 * time.Microsecond)
		}
	}()

	var last int64
	deadline := time.After(3 * time.Second)
	done := false
	for !done {
		select {
		case r := <-ws.Chan():
			if len(r.Events) == 0 {
				if r.Revision < last {
					t.Fatalf("progress rev %d below delivered event rev %d", r.Revision, last)
				}
				last = r.Revision
			} else {
				for _, ev := range r.Events {
					if ev.Kv.ModRevision <= last {
						t.Fatalf("event rev %d not above earlier progress/event rev %d", ev.Kv.ModRevision, last)
					}
					last = ev.Kv.ModRevision
				}
			}
		case <-deadline:
			done = true
		}
	}
	close(stop)
	fin := make(chan struct{})
	go func() {
		// drain so writers' sends never block forever
		for {
			select {
			case <-ws.Chan():
			case <-fin:
				return
			}
		}
	}()
	wait := make(chan struct{})
	go func() { wg.Wait(); close(wait) }()
	select {
	case <-wait:
	case <-time.After(10 * time.Second):
		t.Fatal("deadlock: workers did not stop")
	}
	close(fin)
}
