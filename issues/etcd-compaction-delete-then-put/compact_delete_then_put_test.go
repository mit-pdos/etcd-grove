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

// TestCompactAtDeleteThenPutRevision ensures that compacting at the revision of
// a txn that deletes a key and puts it again keeps the key's value.
func TestCompactAtDeleteThenPutRevision(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	kv := clus.RandClient()
	ctx := t.Context()

	_, err := kv.Put(ctx, "a", "v1")
	require.NoError(t, err)
	resp, err := kv.Txn(ctx).Then(
		clientv3.OpDelete("a", clientv3.WithFromKey()),
		clientv3.OpPut("a", "v2"),
	).Commit()
	require.NoError(t, err)
	rev := resp.Header.Revision

	_, err = kv.Compact(ctx, rev, clientv3.WithCompactPhysical())
	require.NoError(t, err)

	gresp, err := kv.Get(ctx, "a")
	require.NoError(t, err)
	require.Len(t, gresp.Kvs, 1)
	require.Equal(t, "v2", string(gresp.Kvs[0].Value))
}
