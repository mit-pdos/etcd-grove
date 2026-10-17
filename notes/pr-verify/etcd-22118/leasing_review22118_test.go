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
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// A Put inside a Txn into the reserved prefix is not rejected either: it detaches the
// owner's lease key from its session lease and the next writer of the user key blocks.
func TestReview22118TxnPutIntoPrefix(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv1, c1, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer c1()
	lkv2, c2, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer c2()

	_, err = lkv1.Put(t.Context(), "k", "v1")
	require.NoError(t, err)
	_, err = lkv1.Get(t.Context(), "k") // lkv1 owns "pfx/k"
	require.NoError(t, err)

	_, err = lkv2.Txn(t.Context()).Then(clientv3.OpPut("pfx/k", "")).Commit()
	require.NoError(t, err, "txn put into the reserved prefix accepted")

	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Second)
	defer cancel()
	_, err = lkv2.Put(ctx, "k", "v2")
	t.Logf("lkv2.Put(k) after txn put into prefix: err=%v", err)
	resp, gerr := lkv1.Get(t.Context(), "k")
	require.NoError(t, gerr)
	t.Logf("lkv1.Get(k) = %q", resp.Kvs[0].Value)
	require.NoError(t, err)
}

// The rejection takes precedence over a cancelled context, and over an empty range.
func TestReview22118Precedence(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, c, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer c()

	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	_, err = lkv.Delete(ctx, "a", clientv3.WithFromKey())
	t.Logf("cancelled ctx, intersecting delete: %v", err)
	require.Equal(t, codes.InvalidArgument, status.Code(err))

	// Else branch that cannot run (empty If is true) still rejects the whole txn.
	_, err = lkv.Txn(t.Context()).Then(clientv3.OpGet("x")).Else(clientv3.OpDelete("pfx/z")).Commit()
	t.Logf("delete only in the (unreachable) else branch: %v", err)
	require.Equal(t, codes.InvalidArgument, status.Code(err))

	// Nested txn delete is rejected.
	_, err = lkv.Txn(t.Context()).Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete("a", clientv3.WithFromKey())}, nil)).Commit()
	t.Logf("nested txn delete: %v", err)
	require.Equal(t, codes.InvalidArgument, status.Code(err))

	// Do with a Txn op
	_, err = lkv.Do(t.Context(), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete("", clientv3.WithPrefix())}, nil))
	t.Logf("Do(txn delete all): %v", err)
	require.Equal(t, codes.InvalidArgument, status.Code(err))
}
