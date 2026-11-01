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

// TestLeasingTxnOwnerIfMissingKey checks that a transaction answered from the
// cache on a key cached as absent evaluates its comparisons as etcd does.
func TestLeasingTxnOwnerIfMissingKey(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	lkv, closeLKV, err := leasing.NewKV(clus.Client(0), "pfx/")
	require.NoError(t, err)
	defer closeLKV()

	// cache "k" as absent
	resp, err := lkv.Get(t.Context(), "k")
	require.NoError(t, err)
	require.Empty(t, resp.Kvs)

	tests := []struct {
		name string
		cmp  clientv3.Cmp
	}{
		{`CreateRevision("k") < 5`, clientv3.Compare(clientv3.CreateRevision("k"), "<", 5)},
		{`Version("k") = 3`, clientv3.Compare(clientv3.Version("k"), "=", 3)},
		{`Value("k") = ""`, clientv3.Compare(clientv3.Value("k"), "=", "")},
	}
	for _, tt := range tests {
		lresp, err := lkv.Txn(t.Context()).If(tt.cmp).Then(clientv3.OpGet("k")).Commit()
		require.NoError(t, err)
		eresp, err := clus.Client(0).Txn(t.Context()).If(tt.cmp).Then(clientv3.OpGet("k")).Commit()
		require.NoError(t, err)
		assert.Equalf(t, eresp.Succeeded, lresp.Succeeded,
			"%s on a missing key: leasing KV Succeeded=%v, etcd Succeeded=%v", tt.name, lresp.Succeeded, eresp.Succeeded)
	}
}
