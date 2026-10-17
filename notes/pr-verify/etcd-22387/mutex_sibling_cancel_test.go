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

package concurrency_test

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestMutexLockSiblingCanceledSessionAlive: A and B (one session S) wait
// behind C; A's context is canceled (its Lock deletes the shared key). B's
// Lock returns at once with ErrSessionExpired although S is alive.
func TestMutexLockSiblingCanceledSessionAlive(t *testing.T) {
	const pfx = "/mutex-sibling-canceled"
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	sC, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer sC.Close()
	sS, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer sS.Close()

	mC := concurrency.NewMutex(sC, pfx)
	require.NoError(t, mC.Lock(t.Context()))
	aCtx, aCancel := context.WithCancel(t.Context())
	aDone := make(chan error, 1)
	go func() { aDone <- concurrency.NewMutex(sS, pfx).Lock(aCtx) }()
	bDone := make(chan error, 1)
	go func() { bDone <- concurrency.NewMutex(sS, pfx).Lock(t.Context()) }()
	time.Sleep(500 * time.Millisecond)
	aCancel()
	t.Logf("A: %v", <-aDone)
	select {
	case bErr := <-bDone:
		ttl, terr := cli.TimeToLive(t.Context(), sS.Lease())
		require.NoError(t, terr)
		t.Logf("B returned %v while C holds the lock; session S TTL %d (alive: %v)", bErr, ttl.TTL, ttl.TTL > 0)
		require.NotErrorIs(t, bErr, concurrency.ErrSessionExpired, "ErrSessionExpired while the session is alive")
	case <-time.After(2 * time.Second):
		t.Log("B still waiting behind C (code before the PR)")
	}
	require.NoError(t, mC.Unlock(t.Context()))
}
