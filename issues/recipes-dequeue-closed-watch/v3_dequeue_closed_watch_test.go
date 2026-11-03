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
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

type dequeueResult struct {
	val      string
	err      error
	panicked any
}

func dequeueAsync(dequeue func() (string, error)) <-chan dequeueResult {
	resc := make(chan dequeueResult, 1)
	go func() {
		var res dequeueResult
		defer func() {
			res.panicked = recover()
			resc <- res
		}()
		res.val, res.err = dequeue()
	}()
	return resc
}

func waitDequeue(t *testing.T, resc <-chan dequeueResult) dequeueResult {
	select {
	case res := <-resc:
		return res
	case <-time.After(10 * time.Second):
		t.Fatal("Dequeue did not return")
		return dequeueResult{}
	}
}

// TestQueueDequeueClientClosed checks that a Dequeue blocked on an empty
// queue returns an error, and does not panic, when its client is closed
// (which closes the watch channel it waits on).
func TestQueueDequeueClientClosed(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	for _, tc := range []struct {
		name    string
		dequeue func(cli *clientv3.Client) func() (string, error)
	}{
		{"Queue", func(cli *clientv3.Client) func() (string, error) {
			return recipe.NewQueue(cli, "testq").Dequeue
		}},
		{"PriorityQueue", func(cli *clientv3.Client) func() (string, error) {
			return recipe.NewPriorityQueue(cli, "testpq").Dequeue
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			cli, err := clus.NewClientV3(0)
			require.NoError(t, err)
			resc := dequeueAsync(tc.dequeue(cli))

			// let Dequeue find the queue empty and start waiting
			time.Sleep(500 * time.Millisecond)
			select {
			case res := <-resc:
				t.Fatalf("Dequeue on an empty queue returned %+v", res)
			default:
			}
			require.NoError(t, cli.Close())

			res := waitDequeue(t, resc)
			require.Nilf(t, res.panicked, "Dequeue panicked")
			require.Errorf(t, res.err, "Dequeue returned %q without an error", res.val)
		})
	}
}

// TestWaitPrefixEventsCompacted checks that WaitPrefixEvents reports an error
// when etcd cancels its watch because the revision it starts from is compacted.
func TestWaitPrefixEventsCompacted(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)

	var rev int64
	for i := 0; i < 5; i++ {
		resp, err := cli.Put(t.Context(), "other", fmt.Sprint(i))
		require.NoError(t, err)
		rev = resp.Header.Revision
	}
	_, err := cli.Compact(t.Context(), rev, clientv3.WithCompactPhysical())
	require.NoError(t, err)

	ev, err := recipe.WaitPrefixEvents(cli, "testq", rev-2, []mvccpb.Event_EventType{mvccpb.Event_PUT})
	require.Errorf(t, err, "WaitPrefixEvents returned event %v without an error", ev)
}

// TestQueueDequeueCompacted checks that a Dequeue whose watch is cancelled by
// a compaction (past the revision of its Get, before the watch is registered)
// returns an error and does not panic. Whether the compaction comes in time
// is a race (in practice it wins every time): the test tries several times
// and requires every early return to be an error, never a panic.
func TestQueueDequeueCompacted(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	writer := clus.Client(0)

	hits := 0
	for i := 0; i < 5; i++ {
		cli, err := clus.NewClientV3(0)
		require.NoError(t, err)
		resc := dequeueAsync(recipe.NewQueue(cli, "testq").Dequeue)

		var res *dequeueResult
		deadline := time.After(200 * time.Millisecond)
	compact:
		for {
			select {
			case r := <-resc:
				res = &r
				break compact
			case <-deadline:
				break compact
			default:
			}
			resp, err := writer.Put(t.Context(), "other", "x")
			require.NoError(t, err)
			_, err = writer.Compact(t.Context(), resp.Header.Revision)
			require.NoError(t, err)
		}
		if res != nil {
			hits++
			require.Nilf(t, res.panicked, "Dequeue panicked")
			require.Errorf(t, res.err, "Dequeue returned %q without an error", res.val)
		}
		require.NoError(t, cli.Close())
		if res == nil {
			r := waitDequeue(t, resc)
			require.Nilf(t, r.panicked, "Dequeue panicked")
		}
	}
	t.Logf("compaction cancelled the watch in %d of 5 attempts", hits)
}
