package workqueue_test

import (
	"testing"

	"k8s.io/client-go/util/workqueue"
)

// A Done for an item that is queued but was never handed out by Get pushes a
// second copy: two Gets then return the same item.
func TestDoneWithoutGetDuplicates(t *testing.T) {
	q := workqueue.NewTyped[string]()
	defer q.ShutDown()
	q.Add("a")
	q.Done("a")
	k1, _ := q.Get()
	k2, _ := q.Get()
	if k1 == k2 {
		t.Errorf("two concurrent Gets both returned %q", k1)
	}
}

// A second Done for one Get, after the item was re-added while processing.
func TestDoubleDoneDuplicates(t *testing.T) {
	q := workqueue.NewTyped[string]()
	defer q.ShutDown()
	q.Add("a")
	k, _ := q.Get()
	q.Add(k)
	q.Done(k)
	q.Done(k)
	a, _ := q.Get()
	b, _ := q.Get()
	if a == b {
		t.Errorf("after a double Done, two Gets both returned %q", a)
	}
}
