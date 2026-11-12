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
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
	"go.etcd.io/gofail/runtime"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3AuthRangeStreamRevokedMidStream checks that once a user's read
// permission is revoked, a range stream the user opened before sends no more
// keys. Needs the server built with failpoints (make gofail-enable), for
// beforeRangeStreamChunk.
func TestV3AuthRangeStreamRevokedMidStream(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	for i := 0; i < 100; i++ {
		_, err := clus.Client(0).Put(t.Context(), fmt.Sprintf("k%03d", i), "v")
		require.NoError(t, err)
	}
	authSetupUsers(t, integration.ToGRPC(clus.Client(0)).Auth, []user{
		{name: "user1", password: "user1-123", role: "role1", perm: "read", key: "k", end: "l"},
	})
	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)

	rootc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootc.Close()
	userc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "user1", Password: "user1-123"})
	require.NoError(t, err)
	defer userc.Close()

	// The second chunk's read waits 3s, during which the permission is revoked.
	require.NoError(t, runtime.Enable("beforeRangeStreamChunk", `1*off->1*sleep(3000)`))
	defer runtime.Disable("beforeRangeStreamChunk")

	stream, err := integration.ToGRPC(userc).KV.RangeStream(t.Context(), &pb.RangeRequest{Key: []byte("k"), RangeEnd: []byte("l")})
	require.NoError(t, err)
	first, err := stream.Recv()
	require.NoError(t, err)
	require.NotEmpty(t, first.RangeResponse.Kvs)

	_, err = rootc.RoleRevokePermission(t.Context(), "role1", "k", "l")
	require.NoError(t, err)
	_, err = userc.Get(t.Context(), "k000")
	require.ErrorIs(t, err, rpctypes.ErrPermissionDenied, "the revocation is applied")

	var after int
	for {
		resp, err := stream.Recv()
		if err != nil {
			t.Logf("stream ended: %v", err)
			break
		}
		after += len(resp.RangeResponse.Kvs)
	}
	require.Zerof(t, after, "keys sent to user1 after its read permission was revoked")
}
