package wait

import (
	"sync"
	"sync/atomic"

	"go.etcd.io/etcd/pkg/v3/notify"
)

// REQ wait/notify-after-receive: a receive on the channel Receive returned completes only after a
// Notify that ran after the Receive.
// Users: server.go (leaderChanged, firstCommitInTerm), read.go:98,163,195 (the read loop's
// LeaderChanged and FirstCommitInTermNotify), the lessor's demotion.
// Assumes: n is this snippet's (no other Notify); notified is written only here (an invariant over
// the notifier's count: count ≤ notified).
// Specs: Notify.NewNotifier.spec, Notify.Notifier.Receive.spec, Notify.Notifier.Notify.spec;
// laws: notifyChan_recv.
func ReqNotifyAfterReceive(notified *atomic.Int64) {
	n := notify.NewNotifier()
	ch := n.Receive()
	go func() {
		notified.Add(1)
		n.Notify()
	}()
	<-ch
	if notified.Load() == 0 {
		panic("notify: woken without a notification")
	}
}

// REQ wait/notify-concurrent: concurrent notifications never panic (each closes the channel it
// swapped out).
// Users: server.go (the ready handler's leaderChanged.Notify, the apply thread's
// firstCommitInTerm.Notify: different goroutines).
// Specs: Notify.Notifier.Notify.spec.
func ReqNotifyConcurrent() {
	n := notify.NewNotifier()
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { defer wg.Done(); n.Notify() }()
	go func() { defer wg.Done(); n.Notify() }()
	wg.Wait()
}
