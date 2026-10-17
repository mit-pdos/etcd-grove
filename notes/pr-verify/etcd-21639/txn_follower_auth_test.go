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
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// The apply-time permission check of a transaction (authApplierV3.Txn ->
// CheckTxnAuth) runs on every member, on the request each member applies. A
// member that rewrites or drops the transaction's range operations before
// applying it (removeNeedlessRangeReqs, on members with no waiting client)
// checks permissions on a different request than the member serving the
// client, and the two can disagree on whether the transaction is applied.
//
// Both tests run a transaction Then(Put(k2, "foo"), Get(k1)) as a non-root
// user through member 0, then read k2 from every member as root.

// The user may read k1 and write k2 but has no permission on "\x00". The
// member serving the client checks Get(k1): permitted, the put is applied.
// With range operations rewritten to Get("\x00") (PR #21639), the other
// members check Get("\x00"): denied, the put is not applied there.
func TestTxnFollowerAuthRangeRewritten(t *testing.T) {
	testTxnFollowerAuth(t, &authpb.Permission{PermType: authpb.Permission_READWRITE, Key: []byte("k1"), RangeEnd: []byte("k3")})
}

// The user may write k2 but not read k1. The member serving the client
// checks Get(k1): denied, the transaction is not applied. With range
// operations removed (main before #21432), the other members check only the
// put: permitted, the put is applied there.
func TestTxnFollowerAuthRangeRemoved(t *testing.T) {
	testTxnFollowerAuth(t, &authpb.Permission{PermType: authpb.Permission_WRITE, Key: []byte("k2")})
}

func testTxnFollowerAuth(t *testing.T, perm *authpb.Permission) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	ctx := t.Context()
	authc := integration.ToGRPC(clus.Client(0)).Auth
	for _, u := range []struct{ name, role string }{{"root", "root"}, {"user1", "role1"}} {
		_, err := authc.UserAdd(ctx, &pb.AuthUserAddRequest{Name: u.name, Password: "pw", Options: &authpb.UserAddOptions{}})
		require.NoError(t, err)
		_, err = authc.RoleAdd(ctx, &pb.AuthRoleAddRequest{Name: u.role})
		require.NoError(t, err)
		_, err = authc.UserGrantRole(ctx, &pb.AuthUserGrantRoleRequest{User: u.name, Role: u.role})
		require.NoError(t, err)
	}
	_, err := authc.RoleGrantPermission(ctx, &pb.AuthRoleGrantPermissionRequest{Name: "role1", Perm: perm})
	require.NoError(t, err)
	_, err = authc.AuthEnable(ctx, &pb.AuthEnableRequest{})
	require.NoError(t, err)

	rootc := make([]*clientv3.Client, len(clus.Members))
	for i := range clus.Members {
		c, cerr := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(i).Endpoints(), Username: "root", Password: "pw"})
		require.NoError(t, cerr)
		defer c.Close()
		rootc[i] = c
	}
	_, err = rootc[0].Put(ctx, "k1", "v1")
	require.NoError(t, err)
	_, err = rootc[0].Put(ctx, "k2", "v2")
	require.NoError(t, err)

	userc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "user1", Password: "pw"})
	require.NoError(t, err)
	defer userc.Close()
	_, txnErr := userc.Txn(ctx).Then(clientv3.OpPut("k2", "foo"), clientv3.OpGet("k1")).Commit()
	t.Logf("txn through member 0: err=%v", txnErr)

	// A put after the transaction, so that every member has applied it once
	// it has applied this one.
	_, err = rootc[0].Put(ctx, "fence", "x")
	require.NoError(t, err)

	vals := make([]string, len(clus.Members))
	for i := range clus.Members {
		// Linearizable: member i waits until it has applied the fence.
		resp, gerr := rootc[i].Get(ctx, "k2")
		require.NoError(t, gerr)
		require.Len(t, resp.Kvs, 1)
		vals[i] = string(resp.Kvs[0].Value)
	}
	t.Logf("k2 on members 0..2: %q", vals)
	for i := 1; i < len(vals); i++ {
		assert.Equalf(t, vals[0], vals[i], "member %d's k2 differs from member 0's", i)
	}
}
