package swift

import (
	"testing"
	"time"
)

// SWB-14: stopDescs' contract is that no descriptor goroutine runs after it returns, and
// MaxDescRoutines' bound (P2-B) needs routineCount to count the running goroutines. A goroutine
// retiring on its history slot (an int queued before repchan.stop()) used to leave cmdDescs
// before stopDescs' round reached its shard and to decrement routineCount only afterwards: the
// round saw no active descriptor, stopDescs returned, handleSync reset routineCount to 0, and
// the goroutine's decrement made it -1 (one goroutine over the bound in the next epoch).
//
// Deterministic schedule: the test holds cntL, so the retiring goroutine stops at its
// decrement (before the fix: after its removal from cmdDescs; after the fix: before). stopDescs
// runs; when it has returned the test does handleSync's reset (routineCount = 0) and lets the
// goroutine go on. routineCount must stay 0.
func TestIssueSWB14_RetiringGoroutineOutlivesStopDescs(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, false)
	if MaxDescRoutines == 0 {
		t.Fatal("needs descriptor goroutines")
	}
	x := cid(1, 1)
	desc := r.getCmdDesc(x, nil, nil)
	if desc.seq {
		t.Fatal("x's descriptor is sequential")
	}

	r.cntL.Lock()
	desc.msgs <- 0 // x's history slot (the reply goroutine's, sent before repchan.stop())
	time.Sleep(100 * time.Millisecond)
	done := make(chan struct{})
	go func() {
		r.stopDescs()
		close(done)
	}()
	select {
	case <-done:
		r.routineCount = 0 // handleSync, after stopDescs (the test holds cntL)
		r.cntL.Unlock()
	case <-time.After(200 * time.Millisecond):
		r.cntL.Unlock()
		select {
		case <-done:
		case <-time.After(10 * time.Second):
			t.Fatal("stopDescs did not return")
		}
		r.cntL.Lock()
		r.routineCount = 0 // handleSync, after stopDescs
		r.cntL.Unlock()
	}
	time.Sleep(100 * time.Millisecond) // a goroutine still running would decrement now

	r.cntL.Lock()
	c := r.routineCount
	r.cntL.Unlock()
	if c != 0 {
		t.Fatalf("routineCount = %d after stopDescs and handleSync's reset, want 0 "+
			"(a descriptor goroutine ran after stopDescs returned)", c)
	}
	r.historyL.Lock()
	h := r.history[0].cmdId
	r.historyL.Unlock()
	if h != x {
		t.Fatalf("history slot 0 has %v, want x %v", h, x)
	}
}

// SWB-14 (no deadlock, no lost progress): a stop request and the history slot both reach a
// retiring goroutine (the stop is sent while it waits for historyL, before it leaves
// cmdDescs). It records its slot, answers the stop, and stopDescs returns with routineCount 0.
func TestIssueSWB14_StopAndSlotTogether(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, false)
	if MaxDescRoutines == 0 {
		t.Fatal("needs descriptor goroutines")
	}
	x := cid(1, 1)
	desc := r.getCmdDesc(x, nil, nil)
	if desc.seq {
		t.Fatal("x's descriptor is sequential")
	}

	r.historyL.Lock()
	desc.msgs <- 0
	time.Sleep(50 * time.Millisecond) // the goroutine waits for historyL in the slot case
	done := make(chan struct{})
	go func() {
		r.stopDescs()
		close(done)
	}()
	time.Sleep(50 * time.Millisecond) // stopDescs has sent x its stop request
	r.historyL.Unlock()
	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("stopDescs did not return")
	}

	r.cntL.Lock()
	c := r.routineCount
	r.cntL.Unlock()
	if c != 0 {
		t.Fatalf("routineCount = %d after stopDescs, want 0", c)
	}
	r.historyL.Lock()
	h := r.history[0].cmdId
	r.historyL.Unlock()
	if h != x {
		t.Fatalf("history slot 0 has %v, want x %v", h, x)
	}
	if r.cmdDescs.Has(x.String()) {
		t.Fatal("x's retired descriptor is still in cmdDescs")
	}
}
