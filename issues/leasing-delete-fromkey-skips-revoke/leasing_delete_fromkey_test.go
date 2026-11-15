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

// TestLeasingDeleteFromKeyRevokes checks that a WithFromKey delete through one
// leasing KV makes another leasing KV that caches a key in the range stop
// serving it, as a delete of the key alone does. The range does not reach the
// leasing prefix, so the leasing KVs' own keys are not deleted.
func TestLeasingDeleteFromKeyRevokes(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv1, closeLKV1, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV1()
	lkv2, closeLKV2, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV2()

	_, err = clus.Client(0).Put(t.Context(), "z", "v")
	require.NoError(t, err)
	resp, err := lkv1.Get(t.Context(), "z") // lkv1 acquires and caches z
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1)

	_, err = lkv2.Delete(t.Context(), "q", clientv3.WithFromKey())
	require.NoError(t, err)
	resp, err = clus.Client(0).Get(t.Context(), "z")
	require.NoError(t, err)
	require.Empty(t, resp.Kvs, "z is deleted on etcd")

	resp, err = lkv1.Get(t.Context(), "z")
	require.NoError(t, err)
	require.Empty(t, resp.Kvs, "expected the leasing KV not to return z, deleted on etcd")
}
