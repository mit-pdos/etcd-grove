// Package wait holds the requirement snippets of etcd's pkg/wait, pkg/idutil and pkg/notify (batch
// 2c, Spec/go_etcd_io/etcd/pkg/v3/{wait,idutil,notify}/), as the server uses them: the request
// registry (s.w), the applied-index waiters (s.applyWait), the request id generator (s.reqIDGen), the
// leader-change and first-commit notifiers. Each reliance an explicit panic.
package wait

import (
	"sync/atomic"

	"go.etcd.io/etcd/pkg/v3/wait"
)

// REQ wait/register-trigger: a registered id's receiver gets the value its triggerer sent, once;
// registering a fresh id never panics ("dup id").
// Users: v3_server.go:1107,1124 (processInternalRaftRequestOnce), server.go (applyEntryNormal's
// Trigger with the entry's result).
// Assumes: id was never registered before (a fresh id: the server's idutil ids).
// Specs: Wait.New.spec, Wait.list.Register.spec, Wait.list.Trigger.spec; laws: waitToks_take,
// waitRecv_recv (P id x := x is "result").
func ReqRegisterTrigger(id uint64) {
	w := wait.New()
	ch := w.Register(id)
	go w.Trigger(id, "result")
	x := <-ch
	if s, ok := x.(string); !ok || s != "result" {
		panic("register-trigger: wrong value")
	}
}

// REQ wait/give-up: a receiver that gives up triggers its own id with nil; a late trigger of the same
// id (the apply thread's) then finds nothing and never blocks or panics.
// Users: v3_server.go:1117,1129 (the proposal failed or timed out: "GC wait").
// Assumes: id fresh.
// Specs: Wait.list.Register.spec, Wait.list.Trigger.spec (its waitRecv disjunct, then its P id x one).
func ReqGiveUp(id uint64) {
	w := wait.New()
	_ = w.Register(id)
	w.Trigger(id, nil)
	w.Trigger(id, "late")
}

// REQ wait/wait-time: a channel of Wait(d) is closed only once a deadline at least d was triggered,
// and the triggerer's fact at that deadline holds then.
// Users: server.go:985 (applyWait.Trigger(appliedi) after each applied batch), read.go:135
// (ApplyWait(confirmedIndex)), server.go:630 (waitAppliedIndex).
// Assumes: applied is written only here (P d := applied ≥ d, downward closed).
// Specs: Wait.NewTimeList.spec, Wait.timeList.Wait.spec, Wait.timeList.Trigger.spec; laws:
// timeChan_recv.
func ReqWaitTime(applied *atomic.Uint64) {
	tl := wait.NewTimeList()
	ch := tl.Wait(3)
	go func() {
		applied.Store(5)
		tl.Trigger(5)
	}()
	<-ch
	if applied.Load() < 3 {
		panic("wait-time: woken before the deadline was reached")
	}
	<-tl.Wait(2) // already passed: closec
}
