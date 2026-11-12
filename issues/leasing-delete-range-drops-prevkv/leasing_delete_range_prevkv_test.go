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

// TestLeasingDeleteRangePrevKV checks that a range delete through the leasing
// KV returns the deleted key-values when asked to with WithPrevKV, as a
// delete through the client does.
func TestLeasingDeleteRangePrevKV(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	_, err = lkv.Put(t.Context(), "p/a", "1")
	require.NoError(t, err)
	resp, err := lkv.Delete(t.Context(), "p/", clientv3.WithPrefix(), clientv3.WithPrevKV())
	require.NoError(t, err)
	require.Equal(t, int64(1), resp.Deleted)
	require.Len(t, resp.PrevKvs, 1, "expected the deleted key-value with WithPrevKV")
}
