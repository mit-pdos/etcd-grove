// Spec-guided tests of the auto-compactor's specs (the spec-first pilot's phase 2,
// notes/compactor-pilot-plan.md; README.md says how to run them). This file is copied into the
// package `v3compactor` of etcd at the pinned revision (run.sh), so that it can drive the
// compactor's unexported constructors with a fake clock.
//
// Each run builds a compactor over recording fakes of its environment (`RevGetter`,
// `Compactable`), drives the fake clock in random steps, raises the store's revision, pauses and
// resumes at random, and checks every `Compact` call against the pure part of C1's permits, as
// `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Defs.lean` states them (keep the
// two in step):
//
//   - `revPermit RevLb ret r`: 0 < r, and the store had reached r + ret (some `Rev()` before the
//     call returned at least r + ret);
//   - `perPermit RevLb period γf r`: 0 < r, and the store had reached r at a clock time T
//     (`stampAt`: the earliest `Rev()` returning at least r) with T + period ≤ now, or r is the
//     run's first sample (`firstSample`) and T + retry ≤ now (`retryOf period`);
//   - `compactReqIs p r`: the request's `Physical` is false.
//
// It also measures what the specs leave out (the strength margin, phase 1b's metric): whether
// requests' revisions never decrease, whether a paused compactor compacts, whether a stopped one
// does, and how far past the permit's bound each compaction is.
package v3compactor

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"math/rand"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/jonboulle/clockwork"
	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

var (
	specRuns   = flag.Int("spec-runs", 200, "runs per mode")
	specSteps  = flag.Int("spec-steps", 300, "clock steps per run")
	specSeed   = flag.Int64("spec-seed", 0, "first seed (0: from the time)")
	specMutant = flag.String("spec-mutant", "", "check deliberately changed permits instead (comma-separated): "+
		"no-first (periodic: drop the first-sample case), rev-plus-one (revision: r+ret+1 ≤ rev), "+
		"period-plus-retry (periodic: T+period+retry ≤ now), full-window (periodic: T+retentions*retry ≤ now)")
	specVerbose = flag.Bool("spec-v", false, "print every run's events")
)

type sample struct {
	v int64
	t time.Time
}

type compactCall struct {
	r      int64
	phys   bool
	t      time.Time
	paused bool // the driver had paused the compactor
	stoped bool // the driver had stopped it
}

// recRev is the store's revision, monotone, raised by the driver; it records every read.
type recRev struct {
	mu    sync.Mutex
	clock clockwork.Clock
	rev   int64
	reads []sample
}

func (g *recRev) Rev() int64 {
	g.mu.Lock()
	defer g.mu.Unlock()
	g.reads = append(g.reads, sample{g.rev, g.clock.Now()})
	return g.rev
}

func (g *recRev) raise(d int64) {
	g.mu.Lock()
	g.rev += d
	g.mu.Unlock()
}

// recComp records every compaction request and answers with a random outcome: success, the
// revision already compacted (mvcc.ErrCompacted, which the compactor counts as success), or a
// failure.
type recComp struct {
	mu     sync.Mutex
	clock  clockwork.Clock
	rnd    *rand.Rand
	calls  []compactCall
	paused bool
	stoped bool
}

var errOther = errors.New("spec test: compaction failed")

func (c *recComp) Compact(ctx context.Context, r *pb.CompactionRequest) (*pb.CompactionResponse, error) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.calls = append(c.calls, compactCall{r.Revision, r.Physical, c.clock.Now(), c.paused, c.stoped})
	switch x := c.rnd.Intn(10); {
	case x < 6:
		return &pb.CompactionResponse{}, nil
	case x < 8:
		return nil, mvcc.ErrCompacted
	default:
		return nil, errOther
	}
}

func (c *recComp) setPaused(p bool) { c.mu.Lock(); c.paused = p; c.mu.Unlock() }
func (c *recComp) setStopped()      { c.mu.Lock(); c.stoped = true; c.mu.Unlock() }

// margins collects what the specs do not state.
type margins struct {
	compactions, decreasing, whilePaused, afterStop int
	minSlack                                        time.Duration // periodic: min (now - T - period)
	firstCaseUsed                                   int           // periodic: compactions only the first-sample case allows
	minSlackFull                                    time.Duration // periodic, not the first sample: min (now - T - retentions*retry)
	nonFirstSeen                                    bool
}

// stampOf is the earliest clock time at which the store was seen at r or above (`stampAt`).
func stampOf(reads []sample, r int64) (time.Time, bool) {
	for _, s := range reads {
		if s.v >= r {
			return s.t, true
		}
	}
	return time.Time{}, false
}

// maxBefore is the largest revision read at or before t (`RevLb`).
func maxBefore(reads []sample, t time.Time) int64 {
	m := int64(-1)
	for _, s := range reads {
		if !s.t.After(t) && s.v > m {
			m = s.v
		}
	}
	return m
}

type compactor interface {
	Run()
	Stop()
	Pause()
	Resume()
}

// drive runs one compactor for `steps` clock steps of up to `maxStep`, then stops it and steps the
// clock a few more times (a stopped compactor's behaviour, which no spec states).
func drive(t *testing.T, rnd *rand.Rand, fc *clockwork.FakeClock, cp compactor, g *recRev, c *recComp,
	steps int, maxStep time.Duration) {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	cp.Run()
	paused := false
	for i := 0; i < steps; i++ {
		// the goroutine waits on `After`: nothing runs until the clock moves
		if err := fc.BlockUntilContext(ctx, 1); err != nil {
			t.Fatalf("the compactor's goroutine never waited on the clock: %v", err)
		}
		if rnd.Intn(3) == 0 {
			g.raise(int64(rnd.Intn(5)))
		}
		if rnd.Intn(20) == 0 {
			if paused {
				cp.Resume()
				c.setPaused(false)
			} else {
				cp.Pause()
				c.setPaused(true)
			}
			paused = !paused
		}
		fc.Advance(time.Duration(rnd.Int63n(int64(maxStep) + 1)))
	}
	if err := fc.BlockUntilContext(ctx, 1); err != nil {
		t.Fatalf("the compactor's goroutine never waited on the clock: %v", err)
	}
	c.setPaused(false)
	if paused {
		cp.Resume()
	}
	cp.Stop()
	c.setStopped()
	for i := 0; i < 5; i++ {
		fc.Advance(maxStep)
		time.Sleep(time.Millisecond)
	}
}

func checkRevision(t *testing.T, seed int64, ret int64, g *recRev, c *recComp, m *margins) bool {
	ok := true
	prev := int64(-1)
	for _, call := range c.calls {
		m.compactions++
		need := call.r + ret
		if mutant("rev-plus-one") {
			need++
		}
		if !(0 < call.r) || call.phys || maxBefore(g.reads, call.t) < need {
			t.Errorf("seed %d: revision mode (retention %d): Compact(%d, physical=%v) at %v outside revPermit "+
				"(store's revision then %d)", seed, ret, call.r, call.phys, call.t, maxBefore(g.reads, call.t))
			ok = false
		}
		if call.r < prev {
			m.decreasing++
		}
		prev = call.r
		if call.paused {
			m.whilePaused++
		}
		if call.stoped {
			m.afterStop++
		}
	}
	return ok
}

func checkPeriodic(t *testing.T, seed int64, period time.Duration, g *recRev, c *recComp, m *margins) bool {
	ok := true
	retry := time.Duration(retryOfSpec(int64(period)))
	first := int64(-1)
	if len(g.reads) > 0 {
		first = g.reads[0].v
	}
	prev := int64(-1)
	for _, call := range c.calls {
		m.compactions++
		T, seen := stampOf(g.reads, call.r)
		byPeriod := seen && !T.Add(period).After(call.t)
		if mutant("period-plus-retry") {
			byPeriod = seen && !T.Add(period+retry).After(call.t)
		}
		if mutant("full-window") {
			byPeriod = seen && !T.Add(time.Duration(int64(period)/int64(retry)+1)*retry).After(call.t)
		}
		byFirst := seen && call.r == first && !T.Add(retry).After(call.t)
		if mutant("no-first") {
			byFirst = false
		}
		if !(0 < call.r) || call.phys || !(byPeriod || byFirst) {
			t.Errorf("seed %d: periodic mode (period %v, retry %v): Compact(%d, physical=%v) at %v outside perPermit "+
				"(stamp %v, seen %v, first sample %d)", seed, period, retry, call.r, call.phys, call.t, T, seen, first)
			ok = false
		}
		if seen {
			if s := call.t.Sub(T) - period; m.compactions == 1 || s < m.minSlack {
				m.minSlack = s
			}
			if !byPeriod && byFirst {
				m.firstCaseUsed++
			}
			if call.r != first {
				w := time.Duration(int64(period)/int64(retry)+1) * retry
				if s := call.t.Sub(T) - w; !m.nonFirstSeen || s < m.minSlackFull {
					m.minSlackFull, m.nonFirstSeen = s, true
				}
			}
		}
		if call.r < prev {
			m.decreasing++
		}
		prev = call.r
		if call.paused {
			m.whilePaused++
		}
		if call.stoped {
			m.afterStop++
		}
	}
	return ok
}

func mutant(name string) bool {
	for _, m := range strings.Split(*specMutant, ",") {
		if m == name {
			return true
		}
	}
	return false
}

// retryOfSpec is `retryOf` (Defs.lean): min(period, 1h) / 10.
func retryOfSpec(period int64) int64 {
	h := int64(time.Hour)
	if period < h {
		return period / 10
	}
	return h / 10
}

func TestSpecCompactor(t *testing.T) {
	seed0 := *specSeed
	if seed0 == 0 {
		seed0 = time.Now().UnixNano()
	}
	var mr, mp margins
	failed := 0
	for i := 0; i < *specRuns && failed < 5; i++ {
		seed := seed0 + int64(i)
		// revision mode: retention 0..20 revisions (New accepts any; 0 compacts at the current revision)
		{
			rnd := rand.New(rand.NewSource(seed))
			fc := clockwork.NewFakeClock()
			g := &recRev{clock: fc, rev: int64(rnd.Intn(10))}
			c := &recComp{clock: fc, rnd: rand.New(rand.NewSource(seed ^ 0x5eed))}
			ret := int64(rnd.Intn(21))
			rc := newRevision(zap.NewNop(), fc, ret, g, c)
			drive(t, rnd, fc, rc, g, c, *specSteps/10, 2*revInterval)
			if !checkRevision(t, seed, ret, g, c, &mr) {
				failed++
			}
			if *specVerbose {
				fmt.Printf("revision seed %d ret %d: %d reads, %d compactions %v\n", seed, ret, len(g.reads), len(c.calls), c.calls)
			}
		}
		// periodic mode: periods from 10ns (the spec's lower bound) to past the 1h cap
		{
			rnd := rand.New(rand.NewSource(seed))
			fc := clockwork.NewFakeClock()
			g := &recRev{clock: fc, rev: int64(rnd.Intn(10))}
			c := &recComp{clock: fc, rnd: rand.New(rand.NewSource(seed ^ 0x5eed))}
			periods := []time.Duration{10, 19, 20, 100, time.Second, 90 * time.Minute, 3 * time.Hour}
			period := periods[rnd.Intn(len(periods))]
			pc := newPeriodic(zap.NewNop(), fc, period, g, c)
			retry := time.Duration(retryOfSpec(int64(period)))
			drive(t, rnd, fc, pc, g, c, *specSteps, 3*retry)
			if !checkPeriodic(t, seed, period, g, c, &mp) {
				failed++
			}
			if *specVerbose {
				fmt.Printf("periodic seed %d period %v: %d reads, %d compactions\n", seed, period, len(g.reads), len(c.calls))
			}
		}
	}
	fmt.Printf("seeds %d..%d (mutant %q)\n", seed0, seed0+int64(*specRuns)-1, *specMutant)
	fmt.Printf("revision: %d compactions; strength margin: %d with a decreasing revision, %d while paused, %d after Stop\n",
		mr.compactions, mr.decreasing, mr.whilePaused, mr.afterStop)
	fmt.Printf("periodic: %d compactions; strength margin: %d with a decreasing revision, %d while paused, %d after Stop; "+
		"%d allowed only by the first-sample case; min slack past T+period %v; "+
		"not the first sample: min slack past T+retentions*retry %v\n",
		mp.compactions, mp.decreasing, mp.whilePaused, mp.afterStop, mp.firstCaseUsed, mp.minSlack, mp.minSlackFull)
}

// TestSpecRealClock checks the clock's trust boundary (`Proof/github_com/jonboulle/clockwork/
// Defs.lean`) on the real clock, `clockwork.NewRealClock()`: `After(d)`'s channel delivers once the
// clock is `d` past a time `T` no earlier than the call (`clockLb (T + d)`, with `n ≤ T`). And it
// runs the periodic compactor on the real clock, where the first `Rev()` comes some scheduling
// delay after `Run`'s `Now()`: the case `perPermit`'s first-sample disjunct is for.
func TestSpecRealClock(t *testing.T) {
	rc := clockwork.NewRealClock()
	for i := 0; i < 200; i++ {
		d := time.Duration(rand.Int63n(int64(2 * time.Millisecond)))
		before := rc.Now()
		<-rc.After(d)
		if got := rc.Since(before); got < d {
			t.Errorf("After(%v) delivered after %v", d, got)
		}
	}
	var m margins
	for i := 0; i < 10; i++ {
		g := &recRev{clock: rc, rev: 1}
		c := &recComp{clock: rc, rnd: rand.New(rand.NewSource(int64(i)))}
		period := 20 * time.Millisecond
		pc := newPeriodic(zap.NewNop(), rc, period, g, c)
		pc.Run()
		stop := time.After(300 * time.Millisecond)
	loop:
		for {
			select {
			case <-stop:
				break loop
			case <-time.After(time.Millisecond):
				g.raise(1)
			}
		}
		pc.Stop()
		c.setStopped()
		time.Sleep(10 * time.Millisecond)
		c.mu.Lock()
		g.mu.Lock()
		checkPeriodic(t, int64(i), period, g, c, &m)
		g.mu.Unlock()
		c.mu.Unlock()
	}
	fmt.Printf("real clock: %d compactions; %d allowed only by the first-sample case; min slack past T+period %v; "+
		"%d after Stop\n", m.compactions, m.firstCaseUsed, m.minSlack, m.afterStop)
}
