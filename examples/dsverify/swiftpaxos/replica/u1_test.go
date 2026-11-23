package replica

import (
	"fmt"
	"runtime"
	"syscall"
	"testing"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// inFreshNetns runs f on a goroutine locked to an OS thread that has moved to a
// new, empty network namespace (no route at all: a UDP dial to 8.8.8.8 fails).
// The thread is never unlocked, so it exits with the goroutine.
func inFreshNetns(t *testing.T, f func()) (panicked any) {
	done := make(chan any, 1)
	go func() {
		runtime.LockOSThread()
		if err := syscall.Unshare(syscall.CLONE_NEWNET); err != nil {
			done <- fmt.Sprintf("skip: unshare(CLONE_NEWNET): %v", err)
			return
		}
		defer func() { done <- recover() }()
		f()
	}()
	p := <-done
	if s, ok := p.(string); ok && len(s) > 5 && s[:5] == "skip:" {
		t.Skip(s)
	}
	return p
}

// U1: with no latency file (LatencyConf ""), replica.New must not call
// defs.IP() (a UDP dial, outside the lab's model; it panics without a route).
func TestIssueU1_NewWithoutRoute(t *testing.T) {
	if defs.LatencyConf != "" {
		t.Fatal("LatencyConf must be empty")
	}
	var r *Replica
	p := inFreshNetns(t, func() {
		r = New("", 0, 1, []string{"10.77.0.12:7002", "10.77.0.13:7003", "10.77.0.14:7004"},
			false, true, false, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
	})
	if p != nil {
		t.Fatalf("replica.New panicked without a route: %v", p)
	}
	if r == nil || r.Dt != nil {
		t.Fatalf("replica.New: got %v, want a replica with a nil latency table", r)
	}
}
