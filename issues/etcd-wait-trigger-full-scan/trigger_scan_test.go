// Reproduction of issues/etcd-wait-trigger-full-scan.md (etcd-io/etcd#22450).
//
// Drop into package wait of go.etcd.io/etcd/pkg/v3 (directory pkg/wait of upamanyus/etcd at
// 107edf7e4, the pin of etc/goose.py; also etcd-io/etcd main at ea8b59433) and run
//
//	cd pkg && go test ./wait -run TestTriggerCostGrowsWithPendingWaiters -count=1 -v
//
// It passes at the pin, showing the cost: timeList.Trigger(d) visits every registered deadline,
// not only those <= d, so with N waiters registered for future indices each apply batch's
// Trigger costs O(N) while it releases none of them.
package wait

import (
	"testing"
	"time"
)

func triggerCost(pending int) time.Duration {
	tl := NewTimeList()
	for i := 0; i < pending; i++ {
		tl.Wait(uint64(1_000_000 + i)) // linearizable reads waiting for future applied indices
	}
	const rounds = 200
	start := time.Now()
	for d := uint64(1); d <= rounds; d++ { // one Trigger per apply batch, releasing nothing
		tl.Trigger(d)
	}
	return time.Since(start) / rounds
}

func TestTriggerCostGrowsWithPendingWaiters(t *testing.T) {
	small, large := triggerCost(100), triggerCost(100_000)
	t.Logf("Trigger with 100 pending waiters: %v; with 100000: %v", small, large)
	if large < 50*small {
		t.Fatalf("Trigger cost did not grow with the number of pending waiters (bug not reproduced)")
	}
}
