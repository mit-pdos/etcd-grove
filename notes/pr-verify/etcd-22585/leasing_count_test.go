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
	"testing"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// checkCountAgrees compares the leasing KV's answer for key (served from its
// cache) with etcd's, for a plain get and a count-only get.
func checkCountAgrees(t *testing.T, cli *clientv3.Client, lkv clientv3.KV, key string, step string) {
	t.Helper()
	for _, opts := range [][]clientv3.OpOption{nil, {clientv3.WithCountOnly()}} {
		lresp, err := lkv.Get(t.Context(), key, opts...)
		require.NoError(t, err)
		eresp, err := cli.Get(t.Context(), key, opts...)
		require.NoError(t, err)
		require.Lenf(t, lresp.Kvs, len(eresp.Kvs), "%s (opts %d): Kvs", step, len(opts))
		require.Equalf(t, eresp.Count, lresp.Count, "%s (opts %d): Count, leasing KV vs etcd", step, len(opts))
	}
}

// TestLeasingDeleteCount: a cached key deleted through the leasing KV
// (leasingKV.Delete -> leaseCache.Delete); then put again (leaseCache.Update).
func TestLeasingDeleteCount(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)

	lkv, closeLKV, err := leasing.NewKV(cli, "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = lkv.Put(t.Context(), "k", "v")
	require.NoError(t, err)
	checkCountAgrees(t, cli, lkv, "k", "after put")

	_, err = lkv.Delete(t.Context(), "k")
	require.NoError(t, err)
	checkCountAgrees(t, cli, lkv, "k", "after delete")

	_, err = lkv.Put(t.Context(), "k", "v2")
	require.NoError(t, err)
	checkCountAgrees(t, cli, lkv, "k", "after put again")
}

// TestLeasingTxnDeleteCount: a cached key deleted by a transaction through the
// leasing KV (txnLeasing.commitToCache -> leaseCache.delete).
func TestLeasingTxnDeleteCount(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)

	lkv, closeLKV, err := leasing.NewKV(cli, "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = lkv.Put(t.Context(), "k", "v")
	require.NoError(t, err)
	checkCountAgrees(t, cli, lkv, "k", "after put")

	tresp, err := lkv.Txn(t.Context()).Then(clientv3.OpDelete("k")).Commit()
	require.NoError(t, err)
	require.True(t, tresp.Succeeded)
	checkCountAgrees(t, cli, lkv, "k", "after txn delete")
}
