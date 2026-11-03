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
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestTxnCompareOnlyLinearizable ensures that a txn with comparisons and no
// operations is linearizable: a member cut off from the leader must not answer
// it without a put that returned before it.
func TestTxnCompareOnlyLinearizable(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	leader := clus.WaitLeader(t)
	follower := (leader + 1) % 3
	clus.Members[follower].InjectPartition(t, clus.Members[leader], clus.Members[(leader+2)%3])

	presp, err := clus.Client(leader).Put(t.Context(), "foo", "bar")
	require.NoError(t, err)

	ctx, cancel := context.WithTimeout(t.Context(), time.Second)
	defer cancel()
	tresp, err := clus.Client(follower).Txn(ctx).If(clientv3.Compare(clientv3.Version("foo"), "=", 0)).Commit()
	if err == nil {
		require.GreaterOrEqualf(t, tresp.Header.Revision, presp.Header.Revision, "txn answered without the put (succeeded: %v)", tresp.Succeeded)
	}
}
