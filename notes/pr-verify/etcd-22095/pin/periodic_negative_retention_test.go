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
	"time"

	"github.com/jonboulle/clockwork"
	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

type negCompactable struct {
	mu   sync.Mutex
	revs []int64
}

func (c *negCompactable) Compact(ctx context.Context, r *pb.CompactionRequest) (*pb.CompactionResponse, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.revs = append(c.revs, r.Revision)
	return &pb.CompactionResponse{}, nil
}

type countingRev struct {
	calls atomic.Int64
	rev   atomic.Int64
}

func (r *countingRev) Rev() int64 { r.calls.Add(1); return r.rev.Load() }

// TestPeriodicNegativeRetention shows what `--auto-compaction-mode=periodic
// --auto-compaction-retention=-1h` (accepted by parseCompactionRetention: a
// negative duration) does: the retry interval is negative, so clock.After fires at
// once and the compactor's goroutine spins without sleeping, and the first
// compaction is at the store's current revision: it keeps no history.
func TestPeriodicNegativeRetention(t *testing.T) {
	rg := &countingRev{}
	rg.rev.Store(1000)
	c := &negCompactable{}
	pc := newPeriodic(zap.NewNop(), clockwork.NewRealClock(), -time.Hour, rg, c)
	pc.Run()
	time.Sleep(100 * time.Millisecond)
	pc.Stop()
	time.Sleep(10 * time.Millisecond)

	c.mu.Lock()
	revs := append([]int64(nil), c.revs...)
	c.mu.Unlock()
	calls := rg.calls.Load()
	t.Logf("in 100ms: %d calls to Rev() (the loop does not sleep); compactions at %v (store at revision 1000)", calls, revs)
	if calls < 1000 {
		t.Fatalf("expected a busy loop, got %d Rev() calls", calls)
	}
	if len(revs) == 0 || revs[0] != 1000 {
		t.Fatalf("expected a compaction at the current revision 1000, got %v", revs)
	}
}
