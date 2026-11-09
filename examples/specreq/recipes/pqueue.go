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
// Assumes (compaction): exactFrom from revision 1 (Queue) / the call's start (PriorityQueue): the
// Dequeue specs give the front (the order) only under it, on every path (verify-round A3 F3).
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

// REQ recipes/pqueue-same-priority: two items of one priority get distinct keys in enqueue order,
// so both are dequeued, the first one first.
// Users: T/v3_queue_test.go:99-116 ("[0, 2] priority for priority collision to test seq keys").
// Assumes: every key with the byte prefix key+"/" is the queue's (owned), none at the start.
// Assumes (compaction): exactFrom from revision 1 (Queue) / the call's start (PriorityQueue): the
// Dequeue specs give the front (the order) only under it, on every path (verify-round A3 F3).
// Specs: PriorityQueue.Enqueue.spec (the read's revision R and seqNext: the new key is one past the
// last at R, __prefix unchanged since), Fmt.Sscanf_d.spec, PriorityQueue.Dequeue.spec.
func ReqSamePriority(c *clientv3.Client, key string) {
	q := recipe.NewPriorityQueue(c, key)
	if err := q.Enqueue("first", 1); err != nil {
		return
	}
	if err := q.Enqueue("second", 1); err != nil {
		return
	}
	for _, want := range []string{"first", "second"} {
		v, err := q.Dequeue()
		if err != nil {
			return
		}
		if v != want {
			panic("pqueue-same-priority: lost or reordered")
		}
	}
}

// REQ recipes/pqueue-once: concurrent consumers of a priority queue never get the same item twice,
// and items of one priority are not lost (distinct keys).
// Users: T/v3_queue_test.go:119-127, 222-231 (flatPriorityQueue with priorities 0 and 1).
// Assumes: key+"/" owned, empty at the start.
// No compaction assumption: the claimed key under the prefix and the value are unconditional
// (second pass).
// Specs: PriorityQueue.Enqueue.spec, PriorityQueue.Dequeue.spec.
func ReqPQEveryItemOnce(c *clientv3.Client, key string) {
	q := recipe.NewPriorityQueue(c, key)
	if err := q.Enqueue("x", 0); err != nil {
		return
	}
	if err := q.Enqueue("y", 0); err != nil {
		return
	}
	got := make(chan string, 2)
	for i := 0; i < 2; i++ {
		go func() {
			v, err := recipe.NewPriorityQueue(c, key).Dequeue()
			if err != nil {
				v = ""
			}
			got <- v
		}()
	}
	v1, v2 := <-got, <-got
	if v1 != "" && v1 == v2 {
		panic("pqueue-once: one item dequeued twice")
	}
}
