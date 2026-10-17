package recipes_test

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"
	integration2 "go.etcd.io/etcd/tests/v3/framework/integration"
)

func dump(t *testing.T, cli *clientv3.Client) int {
	resp, err := cli.Get(context.TODO(), "prq/", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	for _, kv := range resp.Kvs {
		t.Logf("%s = %s", kv.Key, kv.Value)
	}
	return len(resp.Kvs)
}

// One item at 100000 with a high seq; then repeated enqueues at 10000 all get the same key.
func TestProbeRepeatedOverwrite(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()
	q := recipe.NewPriorityQueue(cli, "prq")
	for _, v := range []string{"x0", "x1", "x2"} {
		if err := q.EnqueueUint64(v, 100000); err != nil {
			t.Fatal(err)
		}
	}
	for _, v := range []string{"a", "b", "c"} {
		if err := q.EnqueueUint64(v, 10000); err != nil {
			t.Fatal(err)
		}
	}
	if n := dump(t, cli); n != 6 {
		t.Errorf("%d items after 6 enqueues", n)
	}
}

// Uint16 Enqueue at 10000 mixed with EnqueueUint64 at 100000..
func TestProbeMixEnqueue(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()
	q := recipe.NewPriorityQueue(cli, "prq")
	q.EnqueueUint64("big", 100001)
	q.Enqueue("a", 10000)
	q.Enqueue("b", 10000)
	if n := dump(t, cli); n != 3 {
		t.Errorf("%d items after 3 enqueues", n)
	}
}

// Nanosecond timestamps (19 digits) only: fine; mixed with a small priority: order wrong.
func TestProbeTimestamps(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()
	q := recipe.NewPriorityQueue(cli, "prq")
	now := uint64(time.Now().UnixNano())
	q.EnqueueUint64("later", now+1000)
	q.EnqueueUint64("now", now)
	q.EnqueueUint64("urgent", 5)
	dump(t, cli)
	for _, want := range []string{"urgent", "now", "later"} {
		s, err := q.Dequeue()
		if err != nil {
			t.Fatal(err)
		}
		if s != want {
			t.Errorf("Dequeue = %q, want %q", s, want)
		}
	}
}
