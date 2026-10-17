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
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingPutIntoPrefixBlocksWriters: a Put through the leasing KV to a key under the
// leasing prefix is not rejected (etcd#22118 reserves the prefix for deletes only). It
// overwrites the owner's lease key with one that has no lease, so the owner's lease monitor no
// longer recognizes the revoke of another client, which then waits forever for the lease key's
// deletion: a write of the user key through any other leasing KV blocks until its context ends.
func TestLeasingPutIntoPrefixBlocksWriters(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv1, closeLKV1, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV1()
	lkv2, closeLKV2, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV2()

	_, err = lkv1.Put(t.Context(), "b", "v1")
	require.NoError(t, err)
	_, err = lkv1.Get(t.Context(), "b") // lkv1 acquires "pfx/b"
	require.NoError(t, err)

	// A write into the reserved prefix: accepted.
	_, err = lkv2.Put(t.Context(), "pfx/b", "x")
	require.NoError(t, err)
	resp, err := clus.Client(0).Get(t.Context(), "pfx/b")
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1)
	require.Equal(t, int64(0), resp.Kvs[0].Lease, "the lease key lost its lease")

	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	_, err = lkv2.Put(ctx, "b", "v2")
	require.NoError(t, err, "a write of %q through another leasing KV blocks", "b")
}

// TestLeasingDeleteFromKeyStaleRead: what etcd#22083's delete leads to. A WithFromKey delete
// through the leasing KV that removes the lease key of a cached key lets another client's write
// of that key go through without a revoke, and the holder keeps serving the old value. With
// etcd#22118 the delete is rejected and the read is fresh.
func TestLeasingDeleteFromKeyStaleRead(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv1, closeLKV1, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV1()
	lkv2, closeLKV2, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV2()

	_, err = lkv1.Put(t.Context(), "a", "old")
	require.NoError(t, err)
	_, err = lkv1.Get(t.Context(), "a") // lkv1 caches "a", lease key "pfx/a"
	require.NoError(t, err)

	_, err = lkv1.Delete(t.Context(), "b", clientv3.WithFromKey()) // "pfx/a" is in ["b", ...)
	t.Logf("Delete(b, WithFromKey) error: %v", err)

	_, err = lkv2.Put(t.Context(), "a", "new")
	require.NoError(t, err)
	resp, err := lkv1.Get(t.Context(), "a")
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1)
	require.Equal(t, "new", string(resp.Kvs[0].Value), "the holder serves a stale cached value")
}

// TestLeasingDeleteReservedPrefixRejected: the cases etcd#22118 rejects, and one it does not:
// an empty range whose start is in the prefix is rejected too (no key would be deleted).
func TestLeasingDeleteReservedPrefixRejected(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = lkv.Delete(t.Context(), "pfx/b", clientv3.WithRange("pfx/a")) // empty range
	require.Error(t, err)
	_, err = lkv.Delete(t.Context(), "a", clientv3.WithRange("pfx/")) // ends at the prefix
	require.NoError(t, err)
}
