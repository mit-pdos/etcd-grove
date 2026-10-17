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

	clientv3 "go.etcd.io/etcd/client/v3"
	lockpb "go.etcd.io/etcd/server/v3/etcdserver/api/v3lock/v3lockpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// A Lock waiter whose token goes stale (an auth revision bump) while it waits, and which then
// has to watch another key (the key it watched went away but an earlier holder is still
// there). etcd-io/etcd#22560 renews the token of the in-process client's KV calls on
// ErrAuthOldRevision, but its watch wrapper only renews when AuthInfoFromCtx fails, which a
// stale-revision token does not: the new watch is refused, and the waiter's Lock fails.
// Fails at the PR head (7a87a72d1), as on main (where the KV calls fail first).
func TestV3LockWaiterRewatchAfterAuthRevisionBump(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, AuthToken: integration.DefaultTokenJWT})
	defer clus.Terminate(t)
	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)

	rootc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootc.Close()
	tok, err := rootc.Authenticate(t.Context(), "root", "123")
	require.NoError(t, err)
	tokc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Token: tok.Token})
	require.NoError(t, err)
	defer tokc.Close()

	lockRoot := integration.ToGRPC(rootc).Lock
	lockTok := integration.ToGRPC(tokc).Lock
	grant := func() int64 {
		l, gerr := rootc.Grant(t.Context(), 60)
		require.NoError(t, gerr)
		return int64(l.ID)
	}

	// A holds the lock; B and then C wait (C watches B's key).
	a, err := lockRoot.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("foo"), Lease: grant()})
	require.NoError(t, err)
	leaseB := grant()
	go lockRoot.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("foo"), Lease: leaseB})
	time.Sleep(300 * time.Millisecond)
	cDone := make(chan error, 1)
	go func() {
		_, cerr := lockTok.Lock(t.Context(), &lockpb.LockRequest{Name: []byte("foo"), Lease: grant()})
		cDone <- cerr
	}()
	time.Sleep(300 * time.Millisecond)

	// The auth revision moves while C waits; then B goes away, so C must watch A's key.
	_, err = rootc.RoleAdd(t.Context(), "bump")
	require.NoError(t, err)
	_, err = rootc.Revoke(t.Context(), clientv3.LeaseID(leaseB))
	require.NoError(t, err)
	time.Sleep(500 * time.Millisecond)

	_, err = lockRoot.Unlock(t.Context(), &lockpb.UnlockRequest{Key: a.Key})
	require.NoError(t, err)
	select {
	case cerr := <-cDone:
		require.NoError(t, cerr, "the waiter gets the lock")
	case <-time.After(5 * time.Second):
		t.Fatal("the waiter did not get the lock")
	}
}
