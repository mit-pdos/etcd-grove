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

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestKVGetKeysOnlyLease asserts that a keys-only Get returns the lease of
// the key, whatever the sort target.
func TestKVGetKeysOnlyLease(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli := clus.RandClient()
	ctx := t.Context()

	lresp, err := cli.Grant(ctx, 60)
	require.NoError(t, err)
	presp, err := cli.Put(ctx, "foo", "bar", clientv3.WithLease(lresp.ID))
	require.NoError(t, err)
	leasedRev := presp.Header.Revision

	targets := []clientv3.SortTarget{clientv3.SortByKey, clientv3.SortByVersion, clientv3.SortByValue}
	for _, target := range targets {
		resp, err := cli.Get(ctx, "foo", clientv3.WithKeysOnly(), clientv3.WithSort(target, clientv3.SortAscend))
		require.NoError(t, err)
		require.Len(t, resp.Kvs, 1)
		assert.Emptyf(t, resp.Kvs[0].Value, "sort target %v", target)
		assert.Equalf(t, int64(lresp.ID), resp.Kvs[0].Lease, "sort target %v", target)
	}

	// The key no longer has the lease, but it had it at leasedRev.
	_, err = cli.Put(ctx, "foo", "bar")
	require.NoError(t, err)
	for _, target := range targets {
		resp, err := cli.Get(ctx, "foo", clientv3.WithKeysOnly(), clientv3.WithRev(leasedRev), clientv3.WithSort(target, clientv3.SortAscend))
		require.NoError(t, err)
		require.Len(t, resp.Kvs, 1)
		assert.Equalf(t, int64(lresp.ID), resp.Kvs[0].Lease, "sort target %v, revision %d", target, leasedRev)
	}
}
