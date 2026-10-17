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

package cache

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"testing"
	"testing/synctest"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// recordingClock is a fakeClock that records the duration of every timer
// except the progress requestor's (skip).
type recordingClock struct {
	*fakeClock
	skip time.Duration
	mu   sync.Mutex
	ds   []time.Duration
	ch   chan struct{}
}

func (r *recordingClock) NewTimer(d time.Duration) Timer {
	if d == r.skip {
		return r.fakeClock.NewTimer(d)
	}
	r.mu.Lock()
	r.ds = append(r.ds, d)
	r.mu.Unlock()
	r.ch <- struct{}{}
	return r.fakeClock.NewTimer(d)
}

type alwaysFailingKV struct{ clientv3.KV }

func (alwaysFailingKV) Get(context.Context, string, ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	return nil, errors.New("upstream unavailable")
}

// TestCacheBackoffStaysPositiveWithLargeMaxBackoff: New accepts
// InitialBackoff = MaxBackoff = 1<<62; after the first retry, backoff *= 2
// wraps to math.MinInt64, which is not above MaxBackoff, so the next timer is
// negative and every later one is 0: the loop then retries without waiting.
func TestCacheBackoffStaysPositiveWithLargeMaxBackoff(t *testing.T) {
	cfg := defaultConfig()
	clk := &recordingClock{fakeClock: newFakeClock(), skip: cfg.ProgressRequestInterval, ch: make(chan struct{}, 16)}
	cfg.InitialBackoff = 1 << 62
	cfg.MaxBackoff = 1 << 62
	c, err := newCache(&clientv3.Client{KV: alwaysFailingKV{}, Watcher: newMockWatcher(8)}, "", cfg, clk)
	if err != nil {
		t.Fatalf("newCache: %v", err)
	}
	defer c.Close()
	wait := func() {
		select {
		case <-clk.ch:
		case <-time.After(5 * time.Second):
			t.Fatal("no retry timer")
		}
	}
	wait()
	clk.Advance(1 << 62)
	wait()
	clk.Advance(0)
	wait()
	clk.mu.Lock()
	ds := append([]time.Duration(nil), clk.ds...)
	clk.mu.Unlock()
	t.Logf("retry timers: %v", ds)
	for i, d := range ds {
		if d < cfg.InitialBackoff || d > cfg.MaxBackoff {
			t.Errorf("retry timer %d is %v, outside [InitialBackoff, MaxBackoff]", i, d)
		}
	}
}

// slowKV answers a Get after delay, unless its context ends first.
type slowKV struct {
	clientv3.KV
	delay time.Duration
	ok    atomic.Int32
	calls atomic.Int32
}

func (s *slowKV) Get(ctx context.Context, _ string, _ ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	s.calls.Add(1)
	select {
	case <-time.After(s.delay):
		s.ok.Add(1)
		return &clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 1}}, nil
	case <-ctx.Done():
		return nil, ctx.Err()
	}
}

// TestCacheBootstrapsWithSlowGet: a bootstrap Get that takes longer than
// GetTimeout (5s by default) — a large prefix — now never completes: every
// attempt hits the deadline and the cache never becomes ready. Before the
// change the first attempt completed after 6s.
func TestCacheBootstrapsWithSlowGet(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		kv := &slowKV{delay: 6 * time.Second}
		c, err := newCache(&clientv3.Client{KV: kv, Watcher: newMockWatcher(8)}, "", defaultConfig(), realClock{})
		if err != nil {
			t.Fatalf("newCache: %v", err)
		}
		time.Sleep(time.Minute)
		c.Close()
		t.Logf("bootstrap Gets: %d started, %d completed", kv.calls.Load(), kv.ok.Load())
		if kv.ok.Load() == 0 {
			t.Errorf("no bootstrap Get completed in a minute (each takes 6s)")
		}
	})
}
