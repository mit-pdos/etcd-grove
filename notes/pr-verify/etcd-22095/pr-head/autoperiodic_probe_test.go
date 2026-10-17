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

package v3compactor

import (
	"context"
	"sync"
	"sync/atomic"
	"testing"

	"github.com/jonboulle/clockwork"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

type constSize struct{ n int64 }

func (s constSize) Size() int64 { return s.n }

type countingCompactable struct {
	mu   sync.Mutex
	revs []int64
}

func (c *countingCompactable) Compact(ctx context.Context, r *pb.CompactionRequest) (*pb.CompactionResponse, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.revs = append(c.revs, r.Revision)
	return &pb.CompactionResponse{}, nil
}

func (c *countingCompactable) count() int {
	c.mu.Lock()
	defer c.mu.Unlock()
	return len(c.revs)
}

type slowRev struct{ rev int64 }

// Rev advances by one revision per call: one write per sample, a nearly idle store.
func (r *slowRev) Rev() int64 { return atomic.AddInt64(&r.rev, 1) }

// TestAutoPeriodicCompactsEveryCooldownOnceAboveHighWater shows that once the
// backend's Size() is above AutoPeriodicHighWater of the quota, the mode
// compacts at every cooldown (1 minute) as long as any revision was written,
// however slowly the store grows: Size() is the file size, which compaction does
// not lower (only a defrag does), so the projection stays above the high-water
// mark for good and the growth rate (0 here) plays no role. With the defaults,
// a store whose file once reached 70% of the quota (after a burst, or restored
// from a large snapshot) is compacted every minute, keeping only the last
// `retention` revisions, from then on.
func TestAutoPeriodicCompactsEveryCooldownOnceAboveHighWater(t *testing.T) {
	fc := clockwork.NewFakeClock()
	c := &countingCompactable{}
	rg := &slowRev{rev: 100}
	// quota 1000, high-water 700; the file is at 800 and does not grow
	ac := newAutoPeriodic(zaptest.NewLogger(t), fc, 5, rg, c, constSize{800}, 1000)
	ac.Run()
	defer ac.Stop()

	const minutes = 10
	steps := int(minutes * AutoPeriodicCooldown / AutoPeriodicSampleInterval)
	for i := 0; i < steps; i++ {
		fc.BlockUntil(1)
		fc.Advance(AutoPeriodicSampleInterval)
	}
	fc.BlockUntil(1)
	n := c.count()
	t.Logf("growth rate 0 B/s, one write per %v: %d compactions in %d minutes", AutoPeriodicSampleInterval, n, minutes)
	if n < minutes-1 {
		t.Fatalf("expected about one compaction per cooldown, got %d", n)
	}
}
