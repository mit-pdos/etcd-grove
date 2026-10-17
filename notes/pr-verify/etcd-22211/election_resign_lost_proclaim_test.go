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

// TestElectionResignAfterLostProclaim: when Proclaim finds the leader key gone it returns
// ErrElectionNotLeader and clears leaderKey but not leaderSession. Resign then sends a guarded
// delete of the empty key, which etcd rejects ("key is not provided"). Before etcd-io/etcd#22211
// that error cleared the state, so the next Resign returned nil; with the PR the state is kept and
// every later Resign fails with the same error.
func TestElectionResignAfterLostProclaim(t *testing.T) {
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s.Close()

	e := concurrency.NewElection(s, "/resign-lost-proclaim/")
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()

	require.NoError(t, e.Campaign(ctx, "a"))
	_, err = cli.Delete(ctx, e.Key())
	require.NoError(t, err)
	require.ErrorIs(t, e.Proclaim(ctx, "b"), concurrency.ErrElectionNotLeader)
	require.Empty(t, e.Key())

	var errs []error
	for i := 0; i < 3; i++ {
		errs = append(errs, e.Resign(ctx))
		t.Logf("Resign #%d: %v", i, errs[i])
	}
	require.NoError(t, errs[2], "Resign should not fail forever once the leader key is gone")
}
