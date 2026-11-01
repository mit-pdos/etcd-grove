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

// TestTxnSiblingPutThenDelete ensures that a txn cannot modify a key twice
// through two nested txns, whatever their order: a put of the key in one nested
// txn and a delete of it in a later sibling must be rejected, as the reverse
// order and the flat txn are.
func TestTxnSiblingPutThenDelete(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	kv := clus.RandClient()
	ctx := t.Context()

	put := clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut("a", "v")}, nil)
	del := clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete("a")}, nil)

	_, err := kv.Txn(ctx).Then(clientv3.OpPut("a", "v"), clientv3.OpDelete("a")).Commit()
	require.ErrorIs(t, err, rpctypes.ErrDuplicateKey, "flat put, delete")
	_, err = kv.Txn(ctx).Then(del, put).Commit()
	require.ErrorIs(t, err, rpctypes.ErrDuplicateKey, "txn(delete), txn(put)")
	_, err = kv.Txn(ctx).Then(put, del).Commit()
	require.ErrorIs(t, err, rpctypes.ErrDuplicateKey, "txn(put), txn(delete)")
}
