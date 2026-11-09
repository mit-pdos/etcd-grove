package recipes

import (
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ recipes/pqueue-order: items enqueued before the dequeues come out in priority order (the
// least priority value first; FIFO among equal priorities).
// Users: T/v3_queue_test.go:93-118 (TestPrQueueOneReaderOneWriter: random priorities, dequeued
// in non-decreasing priority).
// Assumes: every key with the byte prefix key+"/" is the queue's (owned), none at the start; no
// Enqueue during the Dequeues (with one, the call may return a later, lower-priority item:
// nonissues/recipes-pqueue-dequeue-order.md).
// Specs: NewPriorityQueue.spec, PriorityQueue.Enqueue.spec (keys pqPrefix key pr / seqKey: the
// key order is the priority order), PriorityQueue.Dequeue.spec (frontByKey as of σ0, taken after
// the Enqueues: no item before the claimed one was written after σ0, so none is present); the
// model's kvStep (.txn).
func ReqPriorityOrder(c *clientv3.Client, key string) {
	q := recipe.NewPriorityQueue(c, key)
	if err := q.Enqueue("low", 2); err != nil {
		return
	}
	if err := q.Enqueue("high", 0); err != nil {
		return
	}
	if err := q.Enqueue("mid", 1); err != nil {
		return
	}
	for _, want := range []string{"high", "mid", "low"} {
		v, err := q.Dequeue()
		if err != nil {
			return
		}
		if v != want {
			panic("pqueue-order: not the highest priority present")
		}
	}
}
