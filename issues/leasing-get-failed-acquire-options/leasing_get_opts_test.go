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

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingGetWithOptsNonOwner checks that a Get whose lease acquisition
// fails, since another client holds the key's lease, respects the request's
// options.
func TestLeasingGetWithOptsNonOwner(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkvA, closeLKVA, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKVA()

	lkvB, closeLKVB, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKVB()

	presp, err := clus.Client(0).Put(t.Context(), "k", "abc")
	require.NoError(t, err)
	// A acquires the lease on "k"
	_, err = lkvA.Get(t.Context(), "k")
	require.NoError(t, err)

	tests := []struct {
		name string
		opt  clientv3.OpOption
	}{
		{"WithKeysOnly", clientv3.WithKeysOnly()},
		{"WithCountOnly", clientv3.WithCountOnly()},
		{"WithMinModRev", clientv3.WithMinModRev(presp.Header.Revision + 1)},
	}
	for _, tt := range tests {
		// B fails to acquire the lease and asks etcd
		lresp, err := lkvB.Get(t.Context(), "k", tt.opt)
		require.NoError(t, err)
		eresp, err := clus.Client(0).Get(t.Context(), "k", tt.opt)
		require.NoError(t, err)
		assert.Equalf(t, eresp.Count, lresp.Count, "%s: Count: leasing KV %+v, etcd %+v", tt.name, lresp.Kvs, eresp.Kvs)
		if assert.Lenf(t, lresp.Kvs, len(eresp.Kvs), "%s: Kvs: leasing KV %+v, etcd %+v", tt.name, lresp.Kvs, eresp.Kvs) {
			for i := range eresp.Kvs {
				assert.Equalf(t, string(eresp.Kvs[i].Key), string(lresp.Kvs[i].Key), "%s: key", tt.name)
				assert.Equalf(t, string(eresp.Kvs[i].Value), string(lresp.Kvs[i].Value), "%s: value: leasing KV %+v, etcd %+v", tt.name, lresp.Kvs, eresp.Kvs)
			}
		}
	}
}
