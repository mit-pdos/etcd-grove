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

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingPutUncachedOnce checks that a Put through the leasing KV of a key
// it has not cached is applied once.
func TestLeasingPutUncachedOnce(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	presp, err := lkv.Put(t.Context(), "k", "abc", clientv3.WithPrevKV())
	require.NoError(t, err)
	assert.Nilf(t, presp.PrevKv, "put of a fresh key returned a previous key-value")

	gresp, err := clus.Client(0).Get(t.Context(), "k")
	require.NoError(t, err)
	require.Len(t, gresp.Kvs, 1)
	assert.Equalf(t, int64(1), gresp.Kvs[0].Version, "version after one put")
	assert.Equalf(t, gresp.Kvs[0].CreateRevision, gresp.Kvs[0].ModRevision, "mod revision after one put")
	assert.Equalf(t, presp.Header.Revision, gresp.Kvs[0].ModRevision, "mod revision of the put")

	presp, err = lkv.Put(t.Context(), "k", "def", clientv3.WithPrevKV())
	require.NoError(t, err)
	require.NotNil(t, presp.PrevKv)
	assert.Equalf(t, "abc", string(presp.PrevKv.Value), "previous value of the second put")
	assert.Equalf(t, int64(1), presp.PrevKv.Version, "previous version of the second put")

	gresp, err = clus.Client(0).Get(t.Context(), "k")
	require.NoError(t, err)
	require.Len(t, gresp.Kvs, 1)
	assert.Equalf(t, int64(2), gresp.Kvs[0].Version, "version after two puts")
}

// TestLeasingDeleteUncachedOnce checks that a Delete through the leasing KV of
// a key it has not cached is applied once and reports the deleted key.
func TestLeasingDeleteUncachedOnce(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)

	dresp, err := lkv.Delete(t.Context(), "k", clientv3.WithPrevKV())
	require.NoError(t, err)
	assert.Equalf(t, int64(1), dresp.Deleted, "number of keys deleted")
	if assert.Lenf(t, dresp.PrevKvs, 1, "previous key-values of the delete") {
		assert.Equal(t, "abc", string(dresp.PrevKvs[0].Value))
	}

	gresp, err := clus.Client(0).Get(t.Context(), "k")
	require.NoError(t, err)
	assert.Empty(t, gresp.Kvs)
}
