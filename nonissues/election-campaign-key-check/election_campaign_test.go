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
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestElectionCampaignKeyDeleted ensures that Campaign does not elect a
// campaigner whose key was deleted while it waited.
func TestElectionCampaignKeyDeleted(t *testing.T) {
	const prefix = "/key-deleted"

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s1, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s1.Close()
	s2, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s2.Close()
	e1 := concurrency.NewElection(s1, prefix)
	e2 := concurrency.NewElection(s2, prefix)

	require.NoError(t, e1.Campaign(t.Context(), "e1"))
	campaigned := make(chan error, 1)
	go func() { campaigned <- e2.Campaign(t.Context(), "e2") }()
	require.Eventually(t, func() bool {
		resp, gerr := cli.Get(t.Context(), prefix+"/", clientv3.WithPrefix())
		return gerr == nil && len(resp.Kvs) == 2
	}, 5*time.Second, 10*time.Millisecond, "e2's key is not created")

	// Revoking s2's lease deletes e2's key while e2 waits for e1.
	_, err = cli.Revoke(t.Context(), s2.Lease())
	require.NoError(t, err)
	require.NoError(t, e1.Resign(t.Context()))
	// e2 is not the leader, since its key is gone.
	require.Error(t, <-campaigned, "e2 elected after its key was deleted")
}
