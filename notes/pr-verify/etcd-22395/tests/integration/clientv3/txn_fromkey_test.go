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

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestTxnDeleteFromKeyThenIgnorePut is the finding's integration test
// (issues/etcd-txn-delete-then-ignore-put.md, fork branch txn-delete-then-ignore-put
// d9ba0e03c), as a file of its own: a txn that deletes every key from a key on and then puts
// that key is rejected as a duplicate key, as it is when the delete names the key alone. Such
// a put with IgnoreValue or IgnoreLease would find no previous key-value when it runs.
func TestTxnDeleteFromKeyThenIgnorePut(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	kv := clus.RandClient()
	ctx := t.Context()

	_, err := kv.Put(ctx, "a", "v")
	require.NoError(t, err)

	for _, opt := range []clientv3.OpOption{clientv3.WithIgnoreValue(), clientv3.WithIgnoreLease()} {
		_, err = kv.Txn(ctx).Then(clientv3.OpDelete("a", clientv3.WithFromKey()), clientv3.OpPut("a", "", opt)).Commit()
		require.ErrorIs(t, err, rpctypes.ErrDuplicateKey)
	}

	resp, err := kv.Get(ctx, "a")
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1)
	require.Equal(t, "v", string(resp.Kvs[0].Value))

	// a put of a key before the deleted range does not overlap it
	_, err = kv.Txn(ctx).Then(clientv3.OpDelete("b", clientv3.WithFromKey()), clientv3.OpPut("a", "", clientv3.WithIgnoreValue())).Commit()
	require.NoError(t, err)
}
