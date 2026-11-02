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
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestKVGetStreamSortByCreateRevision ensures GetStream sorted by create
// revision without an order returns the keys Get returns, or is rejected as
// unsupported.
func TestKVGetStreamSortByCreateRevision(t *testing.T) {
	if integration.ThroughProxy {
		t.Skip("RangeStream is not supported by the KV client adapter")
	}
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	kv := clus.RandClient()
	ctx := t.Context()

	for _, key := range []string{"k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a"} {
		_, err := kv.Put(ctx, key, "1")
		require.NoError(t, err)
	}

	opts := []clientv3.OpOption{clientv3.WithRange("z"), clientv3.WithKeysOnly(), clientv3.WithSort(clientv3.SortByCreateRevision, clientv3.SortNone)}
	resp, err := kv.Get(ctx, "a", opts...)
	require.NoError(t, err)
	stream, err := kv.GetStream(ctx, "a", opts...)
	require.NoError(t, err)
	streamResp, err := clientv3.GetStreamToGetResponse(stream)
	if status.Code(err) == codes.Unimplemented {
		return
	}
	require.NoError(t, err)

	var keys, streamKeys []string
	for _, kv := range resp.Kvs {
		keys = append(keys, string(kv.Key))
	}
	for _, kv := range streamResp.Kvs {
		streamKeys = append(streamKeys, string(kv.Key))
	}
	require.Equal(t, keys, streamKeys)
}
