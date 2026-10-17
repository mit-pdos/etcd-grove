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
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// cancelOnNthKeyGet cancels the campaign's context just before the n-th
// single-key Get (no options) of a key under pfx, then performs it, so that
// the Get fails with context.Canceled: the context is canceled right after the
// wait for the older keys returned.
type cancelOnNthKeyGet struct {
	clientv3.KV
	pfx    string
	n      int32
	calls  atomic.Int32
	cancel context.CancelFunc
}

func (k *cancelOnNthKeyGet) Get(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	if len(opts) == 0 && len(key) > len(k.pfx) && key[:len(k.pfx)] == k.pfx {
		if k.calls.Add(1) == k.n {
			k.cancel()
		}
	}
	return k.KV.Get(ctx, key, opts...)
}

// TestElectionCampaignCanceledAfterWait: a Campaign whose context is canceled
// after the wait succeeded, during the new existence check, returns the
// context's error but leaves its key in place with the leader session cleared:
// Resign does not delete it, and the key (kept alive by the session) is the
// leader, so every other candidate's Campaign blocks until the session ends.
func TestElectionCampaignCanceledAfterWait(t *testing.T) {
	const prefix = "/campaign-canceled-after-wait"

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	s1, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s1.Close()

	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	// With the PR, an uncontended Campaign makes two single-key Gets of its key:
	// waitDeletes' first Get and the final check. Cancel at the second.
	cli1, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli1.Close()
	cli1.KV = &cancelOnNthKeyGet{KV: cli1.KV, pfx: prefix + "/", n: 2, cancel: cancel}
	s1b, err := concurrency.NewSession(cli1, concurrency.WithLease(s1.Lease()))
	require.NoError(t, err)
	e1 := concurrency.NewElection(s1b, prefix)

	cerr := e1.Campaign(ctx, "candidate1")
	t.Logf("Campaign: %v", cerr)
	if cerr == nil {
		t.Skip("Campaign returned nil: no existence check after the wait (code before the PR)")
	}
	require.ErrorIs(t, cerr, context.Canceled)

	// The caller cleans up as documented: Resign.
	require.NoError(t, e1.Resign(t.Context()))

	resp, err := cli.Get(t.Context(), prefix+"/", clientv3.WithPrefix())
	require.NoError(t, err)
	require.Lenf(t, resp.Kvs, 0, "Campaign failed and Resign succeeded, but its key %q is still there (the leader)", keysOf(resp))
}

// TestElectionCampaignCanceledAfterWaitBlocksOthers: the same, then another
// candidate on its own session cannot become leader.
func TestElectionCampaignCanceledAfterWaitBlocksOthers(t *testing.T) {
	const prefix = "/campaign-canceled-after-wait-blocks"

	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()

	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	cli1, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli1.Close()
	cli1.KV = &cancelOnNthKeyGet{KV: cli1.KV, pfx: prefix + "/", n: 2, cancel: cancel}
	s1, err := concurrency.NewSession(cli1)
	require.NoError(t, err)
	defer s1.Close()
	e1 := concurrency.NewElection(s1, prefix)
	cerr := e1.Campaign(ctx, "candidate1")
	if cerr == nil {
		t.Skip("Campaign returned nil: no existence check after the wait (code before the PR)")
	}
	_ = e1.Resign(t.Context())

	s2, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s2.Close()
	e2 := concurrency.NewElection(s2, prefix)
	cctx, ccancel := context.WithTimeout(t.Context(), 3*time.Second)
	defer ccancel()
	require.NoError(t, e2.Campaign(cctx, "candidate2"), "the second candidate is blocked by the first's key, which nobody holds")
}

func keysOf(resp *clientv3.GetResponse) []string {
	var ks []string
	for _, kv := range resp.Kvs {
		ks = append(ks, string(kv.Key))
	}
	return ks
}
