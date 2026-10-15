# A huge or tiny watch progress interval panics the watch service

- **Status**: open (not reported).
- **Where**: `server/etcdserver/api/v3rpc/watch.go` at the pinned revision (`upamanyus/etcd`
  `bc8b52a50`, the same code as upstream `main`): `GetProgressReportInterval` (lines 99–110),
  `SetProgressReportInterval` (113–117), `NewWatchServer` (77–86: the configured
  `WatchProgressNotifyInterval`, clamped below at `minWatchProgressInterval` = 100 ms but not
  above), `serverWatchStream.sendLoop` (418: `time.NewTicker(interval)`). The flag
  `--watch-progress-notify-interval` (`server/embed/config.go:741`) documents no bound.
- **What happens**: `GetProgressReportInterval` returns `interval + jitter` with
  `jitter = rand.Int63n(interval / 10)`:
  - for an interval above about `(2^63 - 1) * 10 / 11` ns (about 265 years, accepted by the flag
    and by `SetProgressReportInterval`), the sum overflows to a negative duration and every watch
    stream's `sendLoop` panics in `time.NewTicker` ("non-positive interval for NewTicker"); the
    goroutine is not recovered, so the server crashes on the first `Watch` call;
  - for an interval below 10 ns (reachable only through `SetProgressReportInterval`, documented
    "for testing"; `NewWatchServer` clamps the configured value to at least 100 ms),
    `rand.Int63n(0)` panics ("invalid argument to Int63n").

  Reproduction (a test of the package, run without touching the tree with
  `go test -overlay overlay.json -run TestProgressReportInterval ./etcdserver/api/v3rpc/` from
  `server/`, the overlay mapping `etcdserver/api/v3rpc/zz_interval_overflow_test.go` to this file;
  both tests pass, i.e. both panics happen):

  ```go
package v3rpc

import (
	"math"
	"testing"
	"time"
)

// A progress interval close to the largest time.Duration overflows when the jitter is added:
// GetProgressReportInterval returns a negative duration, and sendLoop's time.NewTicker panics.
func TestProgressReportIntervalOverflow(t *testing.T) {
	SetProgressReportInterval(time.Duration(math.MaxInt64))
	defer SetProgressReportInterval(10 * time.Minute)
	overflowed := false
	for i := 0; i < 100; i++ {
		if d := GetProgressReportInterval(); d <= 0 {
			overflowed = true
			defer func() {
				if r := recover(); r == nil {
					t.Fatalf("expected time.NewTicker(%v) to panic", d)
				} else {
					t.Logf("time.NewTicker(%v) panicked: %v", d, r)
				}
			}()
			time.NewTicker(d)
			return
		}
	}
	if !overflowed {
		t.Fatal("no overflow observed")
	}
}

// An interval below 10ns makes the jitter's bound 0: rand.Int63n panics.
func TestProgressReportIntervalTiny(t *testing.T) {
	SetProgressReportInterval(5 * time.Nanosecond)
	defer SetProgressReportInterval(10 * time.Minute)
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("expected GetProgressReportInterval to panic")
		} else {
			t.Logf("GetProgressReportInterval panicked: %v", r)
		}
	}()
	GetProgressReportInterval()
}
  ```

  Output at the pinned revision:

  ```
  === RUN   TestProgressReportIntervalOverflow
      zz_interval_overflow_test.go:22: time.NewTicker(-2559433h58m14.764704985s) panicked: non-positive interval for NewTicker
  --- PASS: TestProgressReportIntervalOverflow (0.00s)
  === RUN   TestProgressReportIntervalTiny
      zz_interval_overflow_test.go:42: GetProgressReportInterval panicked: invalid argument to Int63n
  --- PASS: TestProgressReportIntervalTiny (0.00s)
  ```
- **Expected**: a configured interval is either rejected or clamped (as the lower bound is), and
  `GetProgressReportInterval` never returns a non-positive duration; `SetProgressReportInterval`
  states its precondition (at least 10 ns) or clamps.
- **How the proof handles it**: the interval's resource `intervalP`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvWatch.lean`) holds
  `10 ≤ d ≤ 2^62`; `NewWatchServer.spec` requires the configured interval at most `2^62` and
  `SetProgressReportInterval.spec` a value in that range
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/{NewWatchServer,SetProgressReportInterval}.lean`).
- **Possible fixes**: clamp the configured interval above (say at a year) in `NewWatchServer` as
  it is clamped below; compute the jitter as `rand.Int63n(max(int64(interval)/10, 1))` and add it
  with a saturating sum.
- **Found**: 2026-10-14, the watch slice's unit W-S (`GetProgressReportInterval`'s and
  `sendLoop`'s proofs: `time.NewTicker`'s spec needs a positive period).
