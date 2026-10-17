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

// The PR's regression test (etcd-io/etcd#22211 at 02ea79779), renamed so it can be dropped next to
// the unchanged election_test.go of a checkout without the PR.
// TestElectionResignRetryPR22211 reproduces
// https://github.com/etcd-io/etcd/issues/22123: if Resign's delete
// transaction fails (e.g. because its context is canceled before the
// request reaches etcd), Resign must not forget its local leadership
// state. Otherwise a later Resign call becomes a silent no-op and can
// never remove the still-existing leader key.
func TestElectionResignRetryPR22211(t *testing.T) {
	const prefix = "/resign-retry/"

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s.Close()

	e := concurrency.NewElection(s, prefix)

	ctx, cancel := context.WithTimeout(t.Context(), time.Second*10)
	defer cancel()

	require.NoError(t, e.Campaign(ctx, "candidate1"))
	leaderKey := e.Key()
	require.NotEmpty(t, leaderKey)

	canceledCtx, cancelNow := context.WithCancel(ctx)
	cancelNow()
	err = e.Resign(canceledCtx)
	require.ErrorIs(t, err, context.Canceled)

	// The failed Resign must retain enough state to retry: the leader
	// key must still be there, both locally and in etcd.
	require.Equal(t, leaderKey, e.Key())
	resp, err := cli.Get(ctx, leaderKey)
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1, "leader key should still exist in etcd after the failed Resign")

	// A retried Resign with a valid context should now actually succeed.
	require.NoError(t, e.Resign(ctx))
	require.Empty(t, e.Key())
	resp, err = cli.Get(ctx, leaderKey)
	require.NoError(t, err)
	require.Empty(t, resp.Kvs, "leader key should be gone after the successful retry")
}
