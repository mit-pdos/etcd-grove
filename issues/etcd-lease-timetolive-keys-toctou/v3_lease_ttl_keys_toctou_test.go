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
	"context"
	"errors"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	gofail "go.etcd.io/gofail/runtime"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3LeaseTimeToLiveKeysTOCTOU: LeaseTimeToLive with Keys checks the
// caller's read permission on the keys the lease holds, then looks the lease
// up again and returns the keys it holds then. A key attached to the lease in
// between is returned to a user who may not read it.
func TestV3LeaseTimeToLiveKeysTOCTOU(t *testing.T) {
	t.Run("leader", func(t *testing.T) {
		testV3LeaseTimeToLiveKeysTOCTOU(t, 1, "beforeLookupWhenLeaseTimeToLive")
	})
	t.Run("follower", func(t *testing.T) {
		testV3LeaseTimeToLiveKeysTOCTOU(t, 3, "beforeLookupWhenForwardLeaseTimeToLive")
	})
}

func testV3LeaseTimeToLiveKeysTOCTOU(t *testing.T, size int, fpName string) {
	integration.SkipIfNoGoFail(t)
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: size})
	defer clus.Terminate(t)

	leadIdx := clus.WaitLeader(t)
	// U's member: the leader (size 1), or a follower (the check runs on the
	// follower's lessor, the keys come from the leader's).
	uIdx := leadIdx
	if size > 1 {
		uIdx = (leadIdx + 1) % size
	}

	authSetupRoot(t, integration.ToGRPC(clus.Client(leadIdx)).Auth)
	rootc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(leadIdx).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootc.Close()

	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()

	// U may read "a" only.
	_, err = rootc.UserAdd(ctx, "u", "u-pw")
	require.NoError(t, err)
	_, err = rootc.RoleAdd(ctx, "ra")
	require.NoError(t, err)
	_, err = rootc.RoleGrantPermission(ctx, "ra", "a", "", clientv3.PermissionType(clientv3.PermRead))
	require.NoError(t, err)
	_, err = rootc.UserGrantRole(ctx, "u", "ra")
	require.NoError(t, err)

	lresp, err := rootc.Grant(ctx, 100)
	require.NoError(t, err)
	_, err = rootc.Put(ctx, "a", "va", clientv3.WithLease(lresp.ID))
	require.NoError(t, err)

	uc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(uIdx).Endpoints(), Username: "u", Password: "u-pw"})
	require.NoError(t, err)
	defer uc.Close()

	// Before: U sees exactly the key it may read.
	r0, err := uc.TimeToLive(ctx, lresp.ID, clientv3.WithAttachedKeys())
	require.NoError(t, err)
	require.Equal(t, [][]byte{[]byte("a")}, r0.Keys)
	// U may not read "b".
	_, err = uc.Get(ctx, "b")
	require.Error(t, err)

	require.NoError(t, gofail.Enable(fpName, `sleep("2s")`))
	t.Cleanup(func() {
		if terr := gofail.Disable(fpName); terr != nil && !errors.Is(terr, gofail.ErrDisabled) {
			t.Errorf("failed to disable %s: %v", fpName, terr)
		}
	})

	type result struct {
		resp *clientv3.LeaseTimeToLiveResponse
		err  error
	}
	resCh := make(chan result, 1)
	go func() {
		r, rerr := uc.TimeToLive(ctx, lresp.ID, clientv3.WithAttachedKeys())
		resCh <- result{r, rerr}
	}()

	// While U's request sleeps between the permission check and the lookup,
	// root attaches "b" to the lease.
	time.Sleep(500 * time.Millisecond)
	_, err = rootc.Put(ctx, "b", "secret", clientv3.WithLease(lresp.ID))
	require.NoError(t, err)

	res := <-resCh
	require.NoError(t, res.err)
	keys := make([]string, len(res.resp.Keys))
	for i, k := range res.resp.Keys {
		keys[i] = string(k)
	}
	t.Logf("keys returned to u: %v", keys)
	require.NotContains(t, keys, "b", "LeaseTimeToLive returned a key the caller may not read")
}
