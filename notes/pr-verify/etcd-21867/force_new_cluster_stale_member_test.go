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
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestForceNewClusterWithStaleBackendMember: a member that is in the v3
// backend's members bucket but in neither the WAL's snapshot nor its entries
// (the inconsistency of etcd-io/etcd#20967) gets no ConfChangeRemoveNode
// entry from --force-new-cluster. The member must still end up alone and
// able to make progress.
func TestForceNewClusterWithStaleBackendMember(t *testing.T) {
	integration.BeforeTest(t)
	c := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer c.Terminate(t)

	ctx, cancel := context.WithTimeout(t.Context(), integration.RequestTimeout)
	_, err := c.Members[0].Client.Put(ctx, "/foo", "bar")
	cancel()
	require.NoError(t, err)

	c.Members[0].Stop(t)
	c.Members[1].Terminate(t)
	c.Members[2].Terminate(t)

	// Plant a stale member in m0's backend only.
	lg := zaptest.NewLogger(t)
	be := backend.NewDefaultBackend(lg, filepath.Join(c.Members[0].DataDir, "member", "snap", "db"))
	schema.NewMembershipBackend(lg, be).MustSaveMemberToBackend(&membership.Member{
		ID:             types.ID(0x42),
		RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://127.0.0.1:1"}},
	})
	be.ForceCommit()
	require.NoError(t, be.Close())

	c.Members[0].ForceNewCluster = true
	require.NoError(t, c.Members[0].Restart(t))
	c.WaitMembersForLeader(t, c.Members[:1])
	require.Len(t, c.Members[0].Server.Cluster().Members(), 1)
	clusterMustProgress(t, c.Members[:1])
}
