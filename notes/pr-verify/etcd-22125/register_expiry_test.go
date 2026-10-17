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

package grpcproxy

import (
	"context"
	"runtime"
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/proxy/grpcproxy"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestRegisterSessionExpiryNoGoroutineLeak expires Register's session many
// times (by revoking its lease, which closes the session's keepalive channel
// and so ss.Done()) and checks that the number of goroutines and of leases does
// not grow with the number of expiries.
func TestRegisterSessionExpiryNoGoroutineLeak(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)
	paddr := clus.Members[0].GRPCURL
	prefix := "test-name"
	key := prefix + "/" + paddr

	grpcproxy.Register(zaptest.NewLogger(t), cli, prefix, paddr, 5)

	waitLease := func(prev clientv3.LeaseID) clientv3.LeaseID {
		deadline := time.Now().Add(10 * time.Second)
		for time.Now().Before(deadline) {
			resp, err := cli.Get(context.TODO(), key)
			if err != nil {
				t.Fatal(err)
			}
			if len(resp.Kvs) == 1 && clientv3.LeaseID(resp.Kvs[0].Lease) != prev {
				return clientv3.LeaseID(resp.Kvs[0].Lease)
			}
			time.Sleep(50 * time.Millisecond)
		}
		t.Fatal("no new registration")
		return 0
	}

	const expiries = 20
	var base int
	lease := clientv3.LeaseID(0)
	for i := 0; i < expiries; i++ {
		lease = waitLease(lease)
		if i == 2 {
			time.Sleep(200 * time.Millisecond)
			base = runtime.NumGoroutine()
		}
		if _, err := cli.Revoke(context.TODO(), lease); err != nil {
			t.Fatal(err)
		}
	}
	waitLease(lease)
	time.Sleep(500 * time.Millisecond)
	end := runtime.NumGoroutine()
	leases, err := cli.Leases(context.TODO())
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("goroutines after 3 expiries: %d, after %d: %d; leases alive: %d", base, expiries, end, len(leases.Leases))
	if end-base > 5 {
		t.Fatalf("goroutines grew from %d to %d over %d session expiries", base, end, expiries-3)
	}
	if len(leases.Leases) != 1 {
		t.Fatalf("%d leases alive, want 1", len(leases.Leases))
	}
}
