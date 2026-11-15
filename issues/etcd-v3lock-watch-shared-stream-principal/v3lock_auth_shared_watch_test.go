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
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	lockpb "go.etcd.io/etcd/server/v3/etcdserver/api/v3lock/v3lockpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3LockAuthWaiterOtherUser checks that, with auth enabled, a user waiting
// for a lock under its own prefix acquires it once it is released, while
// another user, with no access to that prefix, is also waiting for a lock.
func TestV3LockAuthWaiterOtherUser(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	authSetupUsers(t, integration.ToGRPC(clus.Client(0)).Auth, []user{
		{name: "a", password: "a-123", role: "ra", key: "/a/", end: "/a0"},
		{name: "b", password: "b-123", role: "rb", key: "/b/", end: "/b0"},
	})
	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)

	type locker struct {
		lc     lockpb.LockClient
		leases [2]int64
	}
	newLocker := func(name, password string) locker {
		c, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: name, Password: password})
		require.NoError(t, err)
		t.Cleanup(func() { c.Close() })
		var l locker
		l.lc = integration.ToGRPC(c).Lock
		for i := range l.leases {
			resp, err := integration.ToGRPC(c).Lease.LeaseGrant(t.Context(), &pb.LeaseGrantRequest{TTL: 30})
			require.NoError(t, err)
			l.leases[i] = resp.ID
		}
		return l
	}
	a, b := newLocker("a", "a-123"), newLocker("b", "b-123")

	// a holds /a/l and a second request of a's waits for it.
	_, err := a.lc.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("/a/l"), Lease: a.leases[0]})
	require.NoError(t, err)
	go a.lc.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("/a/l"), Lease: a.leases[1]})
	time.Sleep(500 * time.Millisecond)

	// b holds /b/l and a second request of b's waits for it.
	b1, err := b.lc.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("/b/l"), Lease: b.leases[0]})
	require.NoError(t, err)
	errc := make(chan error, 1)
	go func() {
		_, err := b.lc.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("/b/l"), Lease: b.leases[1]})
		errc <- err
	}()
	select {
	case err := <-errc:
		t.Fatalf("b's second Lock returned before b's first Unlock: %v", err)
	case <-time.After(500 * time.Millisecond):
	}

	_, err = b.lc.Unlock(t.Context(), &lockpb.UnlockRequest{Key: b1.Key})
	require.NoError(t, err)
	select {
	case err := <-errc:
		require.NoError(t, err, "b's second Lock after b's first Unlock")
	case <-time.After(5 * time.Second):
		t.Fatal("b's second Lock not granted after b's first Unlock")
	}
}
