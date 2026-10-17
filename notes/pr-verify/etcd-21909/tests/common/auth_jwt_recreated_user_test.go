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

package common

import (
	"context"
	"os"
	"testing"
	"time"

	"github.com/golang-jwt/jwt/v5"
	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/tests/v3/framework/config"
	"go.etcd.io/etcd/tests/v3/framework/testutils"
)

// mintJWT signs claims with the test key (RS256), as an external token issuer would.
func mintJWT(t *testing.T, claims jwt.MapClaims) string {
	keyBytes, err := os.ReadFile(defaultKeyPath)
	require.NoError(t, err)
	key, err := jwt.ParseRSAPrivateKeyFromPEM(keyBytes)
	require.NoError(t, err)
	tk, err := jwt.NewWithClaims(jwt.SigningMethodRS256, claims).SignedString(key)
	require.NoError(t, err)
	return tk
}

// TestAuthJWTOnlyRecreatedUserOldToken: with a verify-only JWT provider, a token minted
// for a user (with the then-current auth revision, and no "exp" claim) is still accepted
// after the user is deleted and a new user with the same name is created, and it then
// carries the new user's roles (here root). The test passes at etcd-io/etcd#21909's head
// and fails before it, where the token is rejected with "revision of auth store is old".
func TestAuthJWTOnlyRecreatedUserOldToken(t *testing.T) {
	testRunner.BeforeTest(t)
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	clus := testRunner.NewCluster(ctx, t, config.WithClusterConfig(config.ClusterConfig{ClusterSize: 1, AuthToken: verifyJWTOnlyAuth}))
	defer clus.Close()
	cc := testutils.MustClient(clus.Client())
	testutils.ExecuteUntil(ctx, t, func() {
		authRev, err := setupAuthAndGetRevision(cc, []authRole{testRole}, []authUser{rootUser, testUser})
		require.NoError(t, err)

		// the admin's token: a revision claim above any revision this test reaches, so
		// that it stays valid with or without the PR
		rootToken := mintJWT(t, jwt.MapClaims{"username": rootUserName, "revision": uint64(1) << 40,
			"exp": time.Now().Add(time.Minute).Unix()})
		rootClient := testutils.MustClient(clus.Client(WithAuthToken(rootToken)))

		// the user's token: the current revision, and no "exp" (golang-jwt does not require one)
		userToken := mintJWT(t, jwt.MapClaims{"username": testUserName, "revision": authRev})
		userClient := testutils.MustClient(clus.Client(WithAuthToken(userToken)))
		_, err = userClient.Put(ctx, "foo", "bar", config.PutOptions{})
		require.NoError(t, err)

		// the user is deleted, and a new user of the same name is created, as root
		_, err = rootClient.UserDelete(ctx, testUserName)
		require.NoError(t, err)
		_, err = rootClient.UserAdd(ctx, testUserName, "otherpass", config.UserAddOptions{})
		require.NoError(t, err)
		_, err = rootClient.UserGrantRole(ctx, testUserName, rootRoleName)
		require.NoError(t, err)

		// the old token now acts as the new user, with root's permissions
		_, err = userClient.Put(ctx, "outside-foo", "x", config.PutOptions{})
		require.NoError(t, err, "the deleted user's old token: accepted after #21909, rejected before")
		_, err = userClient.RoleAdd(ctx, "role-made-with-old-token")
		require.NoError(t, err)
	})
}
