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

// TestTxnNestedDeep sends a txn nested 4999 deep (each level a txn holding the
// next one, the innermost one comparison) to a member whose --max-txn-ops
// admits it. The member should either refuse it or apply it, and keep serving.
func TestTxnNestedDeep(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, MaxTxnOps: 10000})
	defer clus.Terminate(t)

	cli := clus.RandClient()
	ctx := t.Context()

	op := clientv3.OpTxn([]clientv3.Cmp{clientv3.Compare(clientv3.Version("k"), "=", 0)}, nil, nil)
	for i := 0; i < 4998; i++ {
		op = clientv3.OpTxn(nil, []clientv3.Op{op}, nil)
	}
	_, err := cli.Txn(ctx).Then(op).Commit()
	t.Logf("nested txn: err = %v", err)

	_, err = cli.Put(ctx, "a", "v")
	require.NoError(t, err)
}
