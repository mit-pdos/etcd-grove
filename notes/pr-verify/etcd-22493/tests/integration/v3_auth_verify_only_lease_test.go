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
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/testutils"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3AuthLeaseExpiryVerifyOnlyJWT: on a member whose JWT provider has only
// a public key (verify-only: `--auth-token=jwt,pub-key=...` without
// `priv-key`), an expired lease must still be revoked, deleting its keys
// (etcd-io/etcd#14616). The lease and its key are made before auth is
// enabled (no client of this member can get a token).
func TestV3AuthLeaseExpiryVerifyOnlyJWT(t *testing.T) {
	// before BeforeTest, which changes the working directory
	verifyOnly := fmt.Sprintf("jwt,pub-key=%s,sign-method=RS256",
		testutils.MustAbsPath("../fixtures/server.crt"))
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, AuthToken: verifyOnly})
	defer clus.Terminate(t)

	api := integration.ToGRPC(clus.Client(0))
	lresp, err := api.Lease.LeaseGrant(t.Context(), &pb.LeaseGrantRequest{TTL: 2})
	require.NoError(t, err)
	_, err = api.KV.Put(t.Context(), &pb.PutRequest{Key: []byte("foo"), Value: []byte("bar"), Lease: lresp.ID})
	require.NoError(t, err)
	authSetupRoot(t, api.Auth)

	// The key is deleted once the leader revokes the expired lease (the
	// member's own store, read directly: no client here has a token).
	srv := clus.Members[0].Server
	deadline := time.Now().Add(10 * time.Second)
	for {
		rresp, err := srv.KV().Range(t.Context(), []byte("foo"), nil, mvcc.RangeOptions{})
		require.NoError(t, err)
		if len(rresp.KVs) == 0 {
			return
		}
		if time.Now().After(deadline) {
			t.Fatalf("lease %016x expired 8s ago and its key is still there", lresp.ID)
		}
		time.Sleep(100 * time.Millisecond)
	}
}
