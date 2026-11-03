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
	"sync/atomic"
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingOwnerDeleteRangeLostResponse checks that a range delete whose
// response is lost after etcd applied it evicts every cached key in the range,
// so later Gets do not serve keys etcd has deleted.
func TestLeasingOwnerDeleteRangeLostResponse(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	// loseDeleteResponse makes the next Txn that deletes a range fail with
	// Unavailable after etcd has applied it, as when the connection drops
	// before the response arrives. Unavailable is not retried for a Txn.
	var loseDeleteResponse atomic.Bool
	interceptor := func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {
		err := invoker(ctx, method, req, reply, cc, opts...)
		if txn, ok := req.(*pb.TxnRequest); ok && err == nil && deletesRange(txn) && loseDeleteResponse.CompareAndSwap(true, false) {
			return status.Error(codes.Unavailable, "injected: response lost")
		}
		return err
	}
	cli, err := integration.NewClient(t, clientv3.Config{
		Endpoints:   clus.Client(0).Endpoints(),
		DialOptions: []grpc.DialOption{grpc.WithChainUnaryInterceptor(interceptor)},
	})
	require.NoError(t, err)
	defer cli.Close()

	lkv, closeLKV, err := leasing.NewKV(cli, "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	for _, k := range []string{"a", "b"} {
		_, err = clus.Client(0).Put(t.Context(), k, "v")
		require.NoError(t, err)
		// cache k
		_, err = lkv.Get(t.Context(), k)
		require.NoError(t, err)
	}

	loseDeleteResponse.Store(true)
	_, err = lkv.Delete(t.Context(), "a", clientv3.WithRange("c"))
	require.Error(t, err)
	require.Falsef(t, loseDeleteResponse.Load(), "expected the range delete to reach etcd")

	for _, k := range []string{"a", "b"} {
		resp, err := clus.Client(0).Get(t.Context(), k)
		require.NoError(t, err)
		require.Emptyf(t, resp.Kvs, "expected %q deleted on etcd, got %+v", k, resp.Kvs)

		resp, err = lkv.Get(t.Context(), k)
		require.NoError(t, err)
		require.Emptyf(t, resp.Kvs, "expected the leasing KV not to return %q, deleted on etcd, got %+v", k, resp.Kvs)
	}
}

func deletesRange(txn *pb.TxnRequest) bool {
	for _, op := range txn.Success {
		if del := op.GetRequestDeleteRange(); del != nil && len(del.RangeEnd) > 0 {
			return true
		}
	}
	return false
}
