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

	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestHashKVLatestAfterCompactZero ensures that HashKV at revision 0 hashes all
// keys at the latest revision, also after a compaction at revision 0.
func TestHashKVLatestAfterCompactZero(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cli := clus.RandClient()
	ctx := t.Context()
	ep := clus.Members[0].GRPCURL

	_, err := cli.Compact(ctx, 0)
	require.NoError(t, err)

	var rev int64
	for _, k := range []string{"a", "b", "c"} {
		resp, perr := cli.Put(ctx, k, "v")
		require.NoError(t, perr)
		rev = resp.Header.Revision
	}

	latest, err := cli.HashKV(ctx, ep, 0)
	require.NoError(t, err)
	atRev, err := cli.HashKV(ctx, ep, rev)
	require.NoError(t, err)

	require.Equal(t, rev, latest.HashRevision, "HashKV(0) should hash the latest revision")
	require.Equal(t, atRev.Hash, latest.Hash, "HashKV(0) and HashKV(%d) at revision %d", rev, rev)
}
