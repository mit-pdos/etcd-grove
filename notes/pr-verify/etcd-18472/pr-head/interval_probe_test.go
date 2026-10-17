// Probes of etcd#18472's compaction interval (package v3compactor, at the PR head
// 7842e283ce2e591e78e9c59f5ed287722782ab08). Each test passes when the behavior it names happens.
package v3compactor

import (
	"context"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/jonboulle/clockwork"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// countingRevGetter returns an increasing revision and counts its calls.
type countingRevGetter struct{ calls, rev atomic.Int64 }

func (g *countingRevGetter) Rev() int64 { g.calls.Add(1); return g.rev.Add(1) }

// recordingCompactable records the revisions it is asked to compact.
type recordingCompactable struct {
	mu   sync.Mutex
	revs []int64
}

func (c *recordingCompactable) Compact(_ context.Context, r *pb.CompactionRequest) (*pb.CompactionResponse, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.revs = append(c.revs, r.Revision)
	return &pb.CompactionResponse{}, nil
}

func (c *recordingCompactable) n() int { c.mu.Lock(); defer c.mu.Unlock(); return len(c.revs) }

// A negative --auto-compaction-interval reaches the revision compactor unchanged (only 0 is
// replaced by the 5-minute default), and clock.After(negative) fires at once: the goroutine
// loops without sleeping, asking the revision getter and compacting on every iteration.
func TestProbeRevisionNegativeIntervalSpins(t *testing.T) {
	rg := &countingRevGetter{}
	c := &recordingCompactable{}
	rc := newRevision(zaptest.NewLogger(t), clockwork.NewRealClock(), 10, -time.Second, rg, c)
	rc.Run()
	time.Sleep(100 * time.Millisecond)
	rc.Stop()
	t.Logf("revision mode, interval -1s: %d calls to Rev() and %d compactions in 100ms", rg.calls.Load(), c.n())
	if rg.calls.Load() < 1000 {
		t.Fatalf("expected the loop to spin, got %d calls", rg.calls.Load())
	}
}

// The same with a 1ns interval: accepted, and the compactor compacts on (nearly) every
// iteration of a loop that barely sleeps.
func TestProbeRevisionTinyIntervalNearSpins(t *testing.T) {
	rg := &countingRevGetter{}
	c := &recordingCompactable{}
	rc := newRevision(zaptest.NewLogger(t), clockwork.NewRealClock(), 10, time.Nanosecond, rg, c)
	rc.Run()
	time.Sleep(100 * time.Millisecond)
	rc.Stop()
	t.Logf("revision mode, interval 1ns: %d calls to Rev() and %d compactions in 100ms", rg.calls.Load(), c.n())
	if c.n() < 100 {
		t.Fatalf("expected many compactions, got %d", c.n())
	}
}

// In the periodic mode the interval only gates compactions on the sampling grid, every
// getRetryInterval() = min(retention, 1h)/10: an interval below it has no effect. With a 1h
// retention (samples every 6 minutes) and a 1-minute interval, the compactor compacts every
// 6 minutes, not every minute.
func TestProbePeriodicIntervalBelowSamplingIsIneffective(t *testing.T) {
	fc := clockwork.NewFakeClock()
	rg := &countingRevGetter{}
	c := &recordingCompactable{}
	pc := newPeriodic(zaptest.NewLogger(t), fc, time.Hour, time.Minute, rg, c)
	pc.Run()
	defer pc.Stop()
	// three hours, a minute at a time
	for i := 0; i < 180; i++ {
		fc.BlockUntil(1)
		fc.Advance(time.Minute)
		time.Sleep(time.Millisecond)
	}
	time.Sleep(10 * time.Millisecond)
	n := c.n()
	t.Logf("periodic mode, retention 1h, interval 1m: %d compactions in 3h (retry interval %v)", n, pc.getRetryInterval())
	if n > 30 {
		t.Fatalf("expected at most one compaction per 6-minute sample, got %d", n)
	}
}

// A negative interval in the periodic mode: after the first compaction, every sample whose
// revision changed compacts (the gap test `elapsed < interval` is never true).
func TestProbePeriodicNegativeInterval(t *testing.T) {
	fc := clockwork.NewFakeClock()
	rg := &countingRevGetter{}
	c := &recordingCompactable{}
	pc := newPeriodic(zaptest.NewLogger(t), fc, time.Hour, -time.Hour, rg, c)
	pc.Run()
	defer pc.Stop()
	for i := 0; i < 180; i++ {
		fc.BlockUntil(1)
		fc.Advance(time.Minute)
		time.Sleep(time.Millisecond)
	}
	time.Sleep(10 * time.Millisecond)
	t.Logf("periodic mode, retention 1h, interval -1h: %d compactions in 3h", c.n())
}
