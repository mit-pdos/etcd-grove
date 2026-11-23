package epaxos

import (
	"testing"
	"time"
)

// executeCommands' SLEEP_TIME_NS, now the integer constant 1000000, was the float constant 1e6:
// the same value in its two uses, time.Sleep's time.Duration and timeout's uint64.
func TestFixSleepConst(t *testing.T) {
	const old = 1e6
	const now = 1000000
	if time.Duration(now) != time.Duration(old) || uint64(now) != uint64(old) {
		t.Fatalf("1000000 and 1e6 differ")
	}
	if time.Duration(now) != time.Millisecond {
		t.Fatalf("1000000 ns is not 1 ms")
	}
	var a, b uint64 = 9999000000, 9999000000
	a += now
	b += old
	if a != b || a < COMMIT_GRACE_PERIOD != (b < COMMIT_GRACE_PERIOD) {
		t.Fatalf("timeout arithmetic differs")
	}
}
