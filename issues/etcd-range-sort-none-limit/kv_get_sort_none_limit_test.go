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

package clientv3test

import (
	"testing"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestKVGetSortNoneLimit ensures that a Get sorted by a target other than the
// key with SortNone, which the server sorts in ascending order, returns the
// first keys of the whole sorted range, as with SortAscend.
func TestKVGetSortNoneLimit(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	kv := clus.RandClient()
	ctx := t.Context()

	// versions: a=3, b=2, c=1
	for _, key := range []string{"c", "b", "b", "a", "a", "a"} {
		_, err := kv.Put(ctx, key, "")
		require.NoError(t, err)
	}

	for _, order := range []clientv3.SortOrder{clientv3.SortNone, clientv3.SortAscend} {
		resp, err := kv.Get(ctx, "a",
			clientv3.WithRange("d"),
			clientv3.WithSort(clientv3.SortByVersion, order),
			clientv3.WithLimit(1),
		)
		require.NoError(t, err)
		require.Lenf(t, resp.Kvs, 1, "order %v", order)
		require.Equalf(t, "c", string(resp.Kvs[0].Key), "order %v", order)
		require.Equalf(t, int64(1), resp.Kvs[0].Version, "order %v", order)
		require.Truef(t, resp.More, "order %v", order)
		require.Equalf(t, int64(3), resp.Count, "order %v", order)
	}
}
