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

package lease_test

import (
	"context"
	"sync/atomic"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/testing/protocmp"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingOwnerPutIgnoreValue checks that a put with WithIgnoreValue of a
// cached key leaves the cached value as etcd does.
func TestLeasingOwnerPutIgnoreValue(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)
	// cache k
	_, err = lkv.Get(t.Context(), "k")
	require.NoError(t, err)

	_, err = lkv.Put(t.Context(), "k", "", clientv3.WithIgnoreValue())
	require.NoError(t, err)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")
}

// TestLeasingOwnerPutWithLease checks that after a put with WithLease of a
// cached key, the leasing KV returns the key with that lease, and does not
// return it once the lease is revoked (etcd deletes the key).
func TestLeasingOwnerPutWithLease(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)
	// cache k
	_, err = lkv.Get(t.Context(), "k")
	require.NoError(t, err)

	lresp, err := clus.Client(0).Grant(t.Context(), 60)
	require.NoError(t, err)
	_, err = lkv.Put(t.Context(), "k", "def", clientv3.WithLease(lresp.ID))
	require.NoError(t, err)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")

	// past the backoff after an eviction, a Get may acquire k again
	time.Sleep(3 * time.Second)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")

	_, err = clus.Client(0).Revoke(t.Context(), lresp.ID)
	require.NoError(t, err)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")
}

// TestLeasingTxnOwnerPutIgnoreValue checks that a transaction's put with
// WithIgnoreValue of a cached key leaves the cached value as etcd does.
func TestLeasingTxnOwnerPutIgnoreValue(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)
	// cache k
	_, err = lkv.Get(t.Context(), "k")
	require.NoError(t, err)

	tresp, err := lkv.Txn(t.Context()).Then(clientv3.OpPut("k", "", clientv3.WithIgnoreValue())).Commit()
	require.NoError(t, err)
	require.True(t, tresp.Succeeded)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")
}

// TestLeasingOwnerPutsOutOfOrder checks that two puts of a cached key whose
// responses arrive in the reverse order of their commits leave the cache with
// etcd's key-value, also between the two responses.
func TestLeasingOwnerPutsOutOfOrder(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints()})
	require.NoError(t, err)
	defer cli.Close()
	hkv := &holdCommitKV{KV: cli.KV}
	cli.KV = hkv
	lkv, closeLKV, err := leasing.NewKV(cli, "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)
	// cache k
	_, err = lkv.Get(t.Context(), "k")
	require.NoError(t, err)

	// The first put commits, and returns only after the second put returned.
	committed, release := hkv.holdNext()
	donec := make(chan error, 1)
	go func() {
		_, perr := lkv.Put(t.Context(), "k", "def")
		donec <- perr
	}()
	<-committed
	_, err = lkv.Put(t.Context(), "k", "ghi")
	require.NoError(t, err)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")

	close(release)
	require.NoError(t, <-donec)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")
}

// TestLeasingOwnerPutDeleteOutOfOrder checks that a put and a delete of a
// cached key whose responses arrive in the reverse order of their commits do
// not leave the deleted key in the cache.
func TestLeasingOwnerPutDeleteOutOfOrder(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints()})
	require.NoError(t, err)
	defer cli.Close()
	hkv := &holdCommitKV{KV: cli.KV}
	cli.KV = hkv
	lkv, closeLKV, err := leasing.NewKV(cli, "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)
	// cache k
	_, err = lkv.Get(t.Context(), "k")
	require.NoError(t, err)

	// The put commits, and returns only after the delete returned.
	committed, release := hkv.holdNext()
	donec := make(chan error, 1)
	go func() {
		_, perr := lkv.Put(t.Context(), "k", "def")
		donec <- perr
	}()
	<-committed
	_, err = lkv.Delete(t.Context(), "k")
	require.NoError(t, err)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")

	close(release)
	require.NoError(t, <-donec)
	requireLeasingGetMatches(t, lkv, clus.Client(0), "k")
}

// requireLeasingGetMatches checks that lkv returns key as kv does.
func requireLeasingGetMatches(t *testing.T, lkv, kv clientv3.KV, key string) {
	t.Helper()
	lresp, err := lkv.Get(t.Context(), key)
	require.NoError(t, err)
	resp, err := kv.Get(t.Context(), key)
	require.NoError(t, err)
	if diff := cmp.Diff(resp.Kvs, lresp.Kvs, protocmp.Transform()); diff != "" {
		t.Errorf("leasing KV's %q differs from etcd's (-etcd +leasing):\n%s", key, diff)
	}
}

// holdCommitKV holds the return of the next transaction it commits once armed
// by holdNext.
type holdCommitKV struct {
	clientv3.KV
	hook atomic.Pointer[func()]
}

// holdNext arms kv: committed is closed when the next transaction has
// committed, which returns once release is closed.
func (kv *holdCommitKV) holdNext() (committed <-chan struct{}, release chan<- struct{}) {
	committedc, releasec := make(chan struct{}), make(chan struct{})
	hook := func() {
		close(committedc)
		<-releasec
	}
	kv.hook.Store(&hook)
	return committedc, releasec
}

func (kv *holdCommitKV) Txn(ctx context.Context) clientv3.Txn {
	return &holdCommitTxn{Txn: kv.KV.Txn(ctx), kv: kv}
}

type holdCommitTxn struct {
	clientv3.Txn
	kv *holdCommitKV
}

func (txn *holdCommitTxn) If(cs ...clientv3.Cmp) clientv3.Txn {
	txn.Txn = txn.Txn.If(cs...)
	return txn
}

func (txn *holdCommitTxn) Then(ops ...clientv3.Op) clientv3.Txn {
	txn.Txn = txn.Txn.Then(ops...)
	return txn
}

func (txn *holdCommitTxn) Else(ops ...clientv3.Op) clientv3.Txn {
	txn.Txn = txn.Txn.Else(ops...)
	return txn
}

func (txn *holdCommitTxn) Commit() (*clientv3.TxnResponse, error) {
	resp, err := txn.Txn.Commit()
	if hook := txn.kv.hook.Swap(nil); hook != nil {
		(*hook)()
	}
	return resp, err
}
