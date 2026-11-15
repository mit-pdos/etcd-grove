package recipes

import (
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ recipes/queue-fifo: with one producer and one consumer, items come out in the order they
// went in.
// Users: T/v3_queue_test.go:44-64 (TestQueueOneReaderOneWriter: five items, dequeued in order).
// Assumes: every key with the byte prefix kp is the queue's (owned), none at the start.
// Assumes (compaction): exactFrom from revision 1 (Queue) / the call's start (PriorityQueue): the
// Dequeue specs give the front (the order) only under it, on every path (verify-round A3 F3).
// Specs: NewQueue.spec, Queue.Enqueue.spec (a new key per item, at increasing revisions),
// Queue.Dequeue.spec (frontByRev at the deletion: the least mod revision present); the model's
// kvStep (.txn).
func ReqFIFO(c *clientv3.Client, kp string) {
	q := recipe.NewQueue(c, kp)
	if err := q.Enqueue("a"); err != nil {
		return
	}
	if err := q.Enqueue("b"); err != nil {
		return
	}
	v, err := q.Dequeue()
	if err != nil {
		return
	}
	if v != "a" {
		panic("queue-fifo: not the oldest item")
	}
	v, err = q.Dequeue()
	if err != nil {
		return
	}
	if v != "b" {
		panic("queue-fifo: not the oldest item")
	}
}

// REQ recipes/queue-once: concurrent consumers never get the same item twice (each item is
// deleted by exactly one Dequeue).
// Users: T/v3_queue_test.go:186-200 (manyReaders), :202-215 (manyWriters), for Queue and
// PriorityQueue.
// Assumes: kp owned, empty at the start.
// No compaction assumption: the claimed key under the prefix and the value are unconditional
// (second pass).
// Specs: Queue.Enqueue.spec, Queue.Dequeue.spec (its update fires at the deletion of a present
// key, once: the transaction's comparison on its mod revision).
func ReqEveryItemOnce(c *clientv3.Client, kp string) {
	q := recipe.NewQueue(c, kp)
	if err := q.Enqueue("x"); err != nil {
		return
	}
	if err := q.Enqueue("y"); err != nil {
		return
	}
	got := make(chan string, 2)
	for i := 0; i < 2; i++ {
		go func() {
			v, err := recipe.NewQueue(c, kp).Dequeue()
			if err != nil {
				v = ""
			}
			got <- v
		}()
	}
	v1, v2 := <-got, <-got
	if v1 != "" && v1 == v2 {
		panic("queue-once: one item dequeued twice")
	}
}

// REQ recipes/dequeue-closed: a Dequeue blocked on an empty queue whose watch closes (the client
// closed, a compacted start revision) returns an error, it does not panic or return a value.
// Users: T/v3_closed_watch_test.go:63-98, :121-167 (issues/recipes-dequeue-closed-watch.md, fixed
// in the fork).
// Assumes: kp owned, empty.
// Specs: Queue.Dequeue.spec (no panic; nil only with a claimed key under kp, unconditionally since
// the second pass), WaitPrefixEvents.spec.
func ReqDequeueClosed(c *clientv3.Client, kp string) {
	done := make(chan struct{})
	go func() {
		defer close(done)
		// the queue stays empty (owned, no Enqueue): nil would mean an item was dequeued
		if _, err := recipe.NewQueue(c, kp).Dequeue(); err == nil {
			panic("dequeue-closed: a value out of an empty queue")
		}
	}()
	_ = c.Close()
	<-done
}

// REQ recipes/queue-wait-then-fed: a consumer waiting on an empty queue gets the oldest item put
// after it started waiting (the watch path: the first put after its read, claimed at its mod
// revision, whose value is that put's).
// Users: T/v3_queue_test.go:45-64 (the reader runs concurrently with the writer and usually finds
// the queue empty).
// Assumes: every key with the byte prefix kp is the queue's (owned), none at the start.
// Assumes (compaction): exactFrom from revision 1 (Queue) / the call's start (PriorityQueue): the
// Dequeue specs give the front (the order) only under it, on every path (verify-round A3 F3).
// Specs: Queue.Dequeue.spec (frontByRev at the claim on every path; the value by kvStep's putOnce),
// Queue.Enqueue.spec, WaitPrefixEvents.spec.
func ReqDequeueWaitThenFed(c *clientv3.Client, kp string) {
	got := make(chan string, 1)
	go func() {
		v, err := recipe.NewQueue(c, kp).Dequeue()
		if err != nil {
			v = ""
		}
		got <- v
	}()
	q := recipe.NewQueue(c, kp)
	if err := q.Enqueue("a"); err != nil {
		return
	}
	if err := q.Enqueue("b"); err != nil {
		return
	}
	if v := <-got; v != "" && v != "a" {
		panic("queue-wait-then-fed: not the oldest item")
	}
}
