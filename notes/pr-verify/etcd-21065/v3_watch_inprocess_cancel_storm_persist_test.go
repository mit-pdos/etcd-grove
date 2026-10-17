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

package integration

import (
	"context"
	"fmt"
	"strconv"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3client"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// Over the in-process client (v3client, the transport of the election and lock services and of
// issues #18879 and #20716), the user closes many watches at once. Afterwards the server must
// hold only the watch left open. The mvcc watcher gauge counts the server's watchers.
func TestV3WatchInProcessCancelStormServerWatchers(t *testing.T) {
	testCancelStormServerWatchers(t, true)
}

// The same over a gRPC connection (a unix socket).
func TestV3WatchGRPCCancelStormServerWatchers(t *testing.T) {
	testCancelStormServerWatchers(t, false)
}

func testCancelStormServerWatchers(t *testing.T, inProcess bool) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	var cli *clientv3.Client
	if inProcess {
		cli = v3client.New(clus.Members[0].Server)
		defer cli.Close()
	} else {
		cli = clus.Client(0)
	}

	watchers := func() int {
		s, err := clus.Members[0].Metric("etcd_debugging_mvcc_watcher_total")
		if err != nil {
			t.Fatal(err)
		}
		n, err := strconv.ParseFloat(s, 64)
		if err != nil {
			t.Fatal(err)
		}
		return int(n)
	}
	base := watchers()

	const n = 2000
	keeper := cli.Watch(context.Background(), "keeper", clientv3.WithCreatedNotify())
	<-keeper
	var cancels []context.CancelFunc
	for i := 0; i < n; i++ {
		ctx, cancel := context.WithCancel(context.Background())
		wc := cli.Watch(ctx, fmt.Sprintf("k%d", i), clientv3.WithCreatedNotify())
		<-wc
		cancels = append(cancels, cancel)
	}
	t.Logf("server watchers with all %d watches open: %d", n+1, watchers()-base)
	for _, cancel := range cancels {
		cancel()
	}
	var left int
	for i := 0; i < 50; i++ {
		time.Sleep(100 * time.Millisecond)
		left = watchers() - base
		if left == 1 {
			break
		}
	}
	// one more event for every closed watch: the client cancels an unknown id on its event
	for i := 0; i < n; i++ {
		if _, err := cli.Put(context.Background(), fmt.Sprintf("k%d", i), "v"); err != nil {
			t.Fatal(err)
		}
	}
	time.Sleep(2 * time.Second)
	left2 := watchers() - base
	// is the stream still alive? the keeper gets its event, a new watch is created
	keeperOK := false
	if _, err := cli.Put(context.Background(), "keeper", "v"); err != nil {
		t.Fatal(err)
	}
	select {
	case r := <-keeper:
		keeperOK = len(r.Events) > 0
	case <-time.After(3 * time.Second):
	}
	newOK := false
	nctx, ncancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer ncancel()
	select {
	case r := <-cli.Watch(nctx, "new", clientv3.WithCreatedNotify()):
		newOK = r.Created
	case <-nctx.Done():
	}
	time.Sleep(10 * time.Second)
	for i := 0; i < n; i++ {
		if _, err := cli.Put(context.Background(), fmt.Sprintf("k%d", i), "v2"); err != nil {
			t.Fatal(err)
		}
	}
	time.Sleep(2 * time.Second)
	t.Logf("REVIEW: 12s later, after a second event for each: %d server watchers", watchers()-base)
	t.Logf("server watchers 5s after closing %d watches: %d; after an event for each: %d (want 1, the keeper); keeper gets its event: %v; a new watch is created: %v",
		n, left, left2, keeperOK, newOK)
	if !keeperOK || !newOK {
		t.Errorf("the watch stream is stuck")
	}
	if left2 != 1 {
		t.Errorf("%d closed watches are still registered on the server", left2-1)
	}
}
