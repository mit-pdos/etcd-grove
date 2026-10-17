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

package integration

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestDowngradeCancelWithoutDowngradeInProgress cancels a downgrade on a cluster where none is
// in progress. The version manager's DowngradeCancel returns ErrNoInflightDowngrade, which the
// gRPC layer maps to "etcdserver: no inflight downgrade job" (and the e2e framework's
// DowngradeCancel expects); the server's downgradeCancel handler only logs it and answers with
// success.
func TestDowngradeCancelWithoutDowngradeInProgress(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	// wait for the cluster version to be decided, so that downgradeCancel does not
	// dereference a nil cluster version (etcd-io/etcd#22574)
	deadline := time.Now().Add(10 * time.Second)
	for clus.Members[0].Server.ClusterVersion() == nil {
		require.True(t, time.Now().Before(deadline), "cluster version not decided")
		time.Sleep(10 * time.Millisecond)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	_, err := clus.RandClient().Downgrade(ctx, clientv3.DowngradeCancel, "")
	require.ErrorContains(t, err, "no inflight downgrade job")
}
