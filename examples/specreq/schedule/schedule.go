// Requirement snippets for pkg/schedule's FIFO scheduler (batch 2d).
package schedule

import (
	"context"
	"sync/atomic"

	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/schedule"
)

// REQ schedule/fifo-chain: jobs run one at a time in the order scheduled, each seeing the state
// the previous one left (the apply loop's applyAll jobs hand the apply thread's progress on).
// Users: server/etcdserver/server.go:761, 841 (run).
// Assumes: lg is a logger; no one else uses sched.
// Specs: NewFIFOScheduler.spec, NewJob.spec, isSched's Schedule and Stop rows (schedTail).
func ReqFifoChain(lg *zap.Logger, n int) {
	sched := schedule.NewFIFOScheduler(lg)
	x := 0
	for i := 1; i <= n; i++ {
		i := i
		sched.Schedule(schedule.NewJob("step", func(context.Context) {
			if x != i-1 {
				panic("fifo-chain: out of order")
			}
			x = i
		}))
	}
	sched.Stop()
	if x != n {
		panic("fifo-chain: a pending job did not run before Stop returned")
	}
}

// REQ schedule/stop-runs-pending: Stop returns only after every job scheduled before it has run
// (run's shutdown needs the last applyAll's state back; mvcc's Close its compactions finished).
// Users: server/etcdserver/server.go:798 (run's deferred sched.Stop), storage/mvcc/kvstore.go:302.
// Assumes: lg is a logger.
// Specs: fifo.Stop.spec (the chain's end comes back).
func ReqStopRunsPending(lg *zap.Logger) {
	sched := schedule.NewFIFOScheduler(lg)
	var done atomic.Bool
	sched.Schedule(schedule.NewJob("last", func(context.Context) { done.Store(true) }))
	sched.Stop()
	if !done.Load() {
		panic("stop-runs-pending: job not run")
	}
}

// REQ schedule/cancelled-ctx: a job sees its context done only once Stop was called (mvcc's
// compaction barrier returns early on a done context, which is right only while closing).
// Users: storage/mvcc/kvstore.go:147, 201 (compactBarrier's select on ctx.Done()).
// Assumes: lg is a logger.
// Specs: Schedule's schedCtx (the context's being done gives Pay), fifo.Stop.spec (takes □ Pay).
func ReqCancelledCtx(lg *zap.Logger) {
	sched := schedule.NewFIFOScheduler(lg)
	var stopping atomic.Bool
	sched.Schedule(schedule.NewJob("barrier", func(ctx context.Context) {
		if ctx.Err() != nil && !stopping.Load() {
			panic("cancelled-ctx: context done before Stop")
		}
	}))
	stopping.Store(true)
	sched.Stop()
}
