// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package recipes_test

import (
	"context"
	"testing"

	clientv3 "go.etcd.io/etcd/client/v3"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"
	integration2 "go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestUint64PrQueueOrderAtSixDigits: priorities of 100000 and more are printed with
// more than five digits by "%05d", so their keys no longer sort by priority:
// "prq/100000/..." < "prq/99999/...", and Dequeue returns priority 100000 first.
func TestUint64PrQueueOrderAtSixDigits(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	q := recipe.NewPriorityQueue(clus.RandClient(), "prq")
	if err := q.EnqueueUint64("pr-99999", 99999); err != nil {
		t.Fatal(err)
	}
	if err := q.EnqueueUint64("pr-100000", 100000); err != nil {
		t.Fatal(err)
	}
	s, err := q.Dequeue()
	if err != nil {
		t.Fatal(err)
	}
	if s != "pr-99999" {
		t.Fatalf("first Dequeue = %q, want %q (the smaller priority)", s, "pr-99999")
	}
}

// TestUint64PrQueueEnqueueOverwrites: newSequentialKV looks up the last key under
// the prefix "prq/10000" with WithLastKey (a prefix range, no trailing "/"), which
// also covers priority 100000's keys "prq/100000/...". With three items at priority
// 10000 (sequence numbers 0, 1, 2) and one at priority 100000 (sequence number 0),
// the next EnqueueUint64 at priority 10000 takes sequence number 0+1 = 1 and its
// put overwrites the item "prq/10000/0000000000000001": an enqueued item is lost.
func TestUint64PrQueueEnqueueOverwrites(t *testing.T) {
	integration2.BeforeTest(t)
	clus := integration2.NewCluster(t, &integration2.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli := clus.RandClient()
	q := recipe.NewPriorityQueue(cli, "prq")
	for _, it := range []struct {
		val string
		pr  uint64
	}{{"a", 10000}, {"b", 10000}, {"c", 10000}, {"x", 100000}, {"d", 10000}} {
		if err := q.EnqueueUint64(it.val, it.pr); err != nil {
			t.Fatal(err)
		}
	}
	resp, err := cli.Get(context.TODO(), "prq/", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	for _, kv := range resp.Kvs {
		t.Logf("%s = %s", kv.Key, kv.Value)
	}
	if len(resp.Kvs) != 5 {
		t.Fatalf("%d items in the queue after 5 enqueues, want 5", len(resp.Kvs))
	}
}
