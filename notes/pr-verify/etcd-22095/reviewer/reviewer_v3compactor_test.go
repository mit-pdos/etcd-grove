package v3compactor

import (
	"context"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/jonboulle/clockwork"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest/observer"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

type rvCompactable struct {
	mu   sync.Mutex
	revs []int64
}

func (c *rvCompactable) Compact(ctx context.Context, r *pb.CompactionRequest) (*pb.CompactionResponse, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.revs = append(c.revs, r.Revision)
	return &pb.CompactionResponse{}, nil
}

type rvRev struct{ rev int64 }

func (r *rvRev) Rev() int64 { return atomic.AddInt64(&r.rev, 1) }

type rvSize struct{ n atomic.Int64 }

func (s *rvSize) Size() int64 { return s.n.Load() }

// New in the periodic mode panics (integer divide by zero in getRetentions)
// for a retention of 1..9ns, which parseCompactionRetention accepts ("5ns").
// The postulate newPeriodic.spec says it returns.
func TestReviewerNewPeriodicTinyRetentionPanics(t *testing.T) {
	for _, d := range []time.Duration{5 * time.Nanosecond, -5 * time.Nanosecond} {
		func() {
			defer func() {
				r := recover()
				t.Logf("New(periodic, %v): recovered panic: %v", d, r)
				if r == nil {
					t.Errorf("expected a panic for %v", d)
				}
			}()
			_, _ = New(nil, ModePeriodic, d, &rvRev{}, &rvCompactable{}, &rvSize{}, 1000)
		}()
	}
}

// The logged "projected-time-to-high-water" overflows: once the file is above
// the high-water mark (Size() does not shrink on compaction) and growth stops,
// the EWMA rate decays geometrically toward 0 and
// time.Duration(float64(highWater-size)/rate) * time.Second wraps around.
func TestReviewerEtaOverflow(t *testing.T) {
	core, logs := observer.New(zapcore.InfoLevel)
	fc := clockwork.NewFakeClock()
	sg := &rvSize{}
	sg.n.Store(800)
	c := &rvCompactable{}
	// quota 1000: high-water 700
	ac := newAutoPeriodic(zap.New(core), fc, 5, &rvRev{rev: 100}, c, sg, 1000)
	ac.Run()
	defer ac.Stop()
	for i := 0; i < 400; i++ {
		fc.BlockUntil(1)
		if i == 1 {
			sg.n.Store(801) // one byte of growth, then idle
		}
		fc.Advance(AutoPeriodicSampleInterval)
	}
	fc.BlockUntil(1)
	var etas []time.Duration
	for _, e := range logs.FilterMessage("starting auto-periodic compaction").All() {
		for _, f := range e.Context {
			if f.Key == "projected-time-to-high-water" {
				etas = append(etas, time.Duration(f.Integer))
			}
		}
	}
	var pos, neg int
	for _, e := range etas {
		if e > 0 {
			pos++
		} else {
			neg++
		}
	}
	t.Logf("all etas: %v", etas); t.Logf("%d compactions; size 801 > high-water 700, so the true eta is negative; logged etas: first %v, last %v; %d positive (wrapped) and %d <= 0", len(etas), etas[:6], etas[len(etas)-6:], pos, neg)
	if pos == 0 {
		t.Errorf("expected a wrapped (positive) eta while the size is above the high-water mark")
	}
}

// Stop does not wait for Run's goroutine: a write to a tuning variable after
// Stop (what the PR's embed test's deferred restores do after e.Close) races
// with the goroutine's read of it. Run with -race.
func TestReviewerStopThenWriteTuningRace(t *testing.T) {
	old := AutoPeriodicSampleInterval
	AutoPeriodicSampleInterval = time.Millisecond
	sg := &rvSize{}
	ac := newAutoPeriodic(zap.NewNop(), clockwork.NewRealClock(), 5, &rvRev{rev: 100}, &rvCompactable{}, sg, 1000)
	ac.Run()
	time.Sleep(20 * time.Millisecond)
	ac.Stop()
	AutoPeriodicSampleInterval = old
}
