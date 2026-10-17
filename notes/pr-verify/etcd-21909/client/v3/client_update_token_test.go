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

package clientv3

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/v3/credentials"
)

// TestUpdateAuthTokenNoCredentialsPanics: a client built without a token or a user name
// and password has no authTokenBundle, and UpdateAuthToken dereferences it.
func TestUpdateAuthTokenNoCredentialsPanics(t *testing.T) {
	c, err := New(Config{Endpoints: []string{"127.0.0.1:0"}})
	require.NoError(t, err)
	defer c.Close()
	require.Panics(t, func() { c.UpdateAuthToken("token") })
}

// TestUpdateAuthTokenRacesWithRetry: UpdateAuthToken writes c.Token while a failing call's
// retry interceptor reads it (shouldRefreshToken). Run with -race.
func TestUpdateAuthTokenRacesWithRetry(t *testing.T) {
	c, err := New(Config{Endpoints: []string{"127.0.0.1:0"}, Token: "token0"})
	require.NoError(t, err)
	defer c.Close()

	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		defer wg.Done()
		for i := 0; i < 1000; i++ {
			c.UpdateAuthToken("token1")
		}
	}()
	go func() {
		defer wg.Done()
		for i := 0; i < 1000; i++ {
			// what unaryClientInterceptor does after a call fails with an auth error
			_ = c.shouldRefreshToken(rpctypes.ErrGRPCInvalidAuthToken, &options{retryAuth: true})
		}
	}()
	wg.Wait()
}

// TestUpdateAuthTokenDisablesPasswordRefresh: on a client built with a user name and
// password, UpdateAuthToken sets c.Token, after which the client never re-authenticates
// on ErrInvalidAuthToken/ErrAuthOldRevision (shouldRefreshToken returns false).
func TestUpdateAuthTokenDisablesPasswordRefresh(t *testing.T) {
	// the fields New sets for a user name and password (New itself would authenticate)
	c := &Client{Username: "u", Password: "p", authTokenBundle: credentials.NewPerRPCCredentialBundle()}
	opts := &options{retryAuth: true}
	require.True(t, c.shouldRefreshToken(rpctypes.ErrGRPCInvalidAuthToken, opts))
	c.UpdateAuthToken("external")
	require.False(t, c.shouldRefreshToken(rpctypes.ErrGRPCInvalidAuthToken, opts))
}
