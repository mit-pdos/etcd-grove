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
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	lockpb "go.etcd.io/etcd/server/v3/etcdserver/api/v3lock/v3lockpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// A token that the KV API rejects (revoked by a password change, or expired) must not be
// accepted by the Lock API either. Passes on main (f061acd09); fails at etcd-io/etcd#22560's
// head (7a87a72d1), where the in-process client renews any such token, on every call (not
// only on calls that were blocked when the token went stale).
func TestV3LockUnlockRejectsRevokedAndExpiredJWT(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, AuthToken: integration.DefaultTokenJWT}) // ttl=2s
	defer clus.Terminate(t)

	authc := integration.ToGRPC(clus.Client(0)).Auth
	authSetupRoot(t, authc)
	rootc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootc.Close()
	authSetupUsers(t, integration.ToGRPC(rootc).Auth, []user{{name: "alice", password: "pwd", role: "rw", key: "foo", end: "fop"}})
	for _, k := range []string{"foo1", "foo2"} {
		_, err = rootc.Put(t.Context(), k, "v")
		require.NoError(t, err)
	}

	leaked, err := rootc.Authenticate(t.Context(), "alice", "pwd")
	require.NoError(t, err)
	alicec, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints(), Token: leaked.Token})
	require.NoError(t, err)
	defer alicec.Close()

	// The administrator revokes the leaked token by changing alice's password.
	_, err = rootc.UserChangePassword(t.Context(), "alice", "new")
	require.NoError(t, err)

	_, err = alicec.Delete(t.Context(), "foo1")
	require.Error(t, err, "KV rejects the revoked token")
	t.Logf("KV Delete with the revoked token: %v", err)
	_, err = integration.ToGRPC(alicec).Lock.Unlock(t.Context(), &lockpb.UnlockRequest{Key: []byte("foo1")})
	t.Logf("Lock.Unlock with the revoked token: %v", err)
	if err == nil {
		t.Errorf("Lock.Unlock accepted the revoked token")
	}

	time.Sleep(3 * time.Second) // the JWT has expired too
	_, err = integration.ToGRPC(alicec).Lock.Unlock(t.Context(), &lockpb.UnlockRequest{Key: []byte("foo2")})
	t.Logf("Lock.Unlock with the revoked, expired token: %v", err)
	if err == nil {
		t.Errorf("Lock.Unlock accepted the revoked, expired token")
	}

	resp, err := integration.ToGRPC(rootc).KV.Range(t.Context(), &pb.RangeRequest{Key: []byte("foo"), RangeEnd: []byte("fop")})
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 2, "both keys survive")
}
