---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/etcd#15656 pr merged: related, not this bug (GHSA-3p4g-rcw5-8298, CVE-2023-32082: added `checkLeaseTimeToLive`, the check this race gets past)
---

# server/etcdserver: `LeaseTimeToLive` with `Keys` returns key names the caller may not read

- **Status**: a bug (an authorization bypass: a time-of-check/time-of-use race). A non-admin
  user who may read some of a lease's keys learns the names of keys attached to the lease after
  its permission check, keys it may not read. Reproduced by an integration test (gofail), on the
  leader and on a follower.
- **Where**: `server/etcdserver/v3_server.go` at 249d76bea (`etc/goose.py`'s etcd pin):
  - `EtcdServer.LeaseTimeToLive` (`v3_server.go:698-723`): with `r.Keys`, calls
    `checkLeaseTimeToLive`, then `leaseTimeToLive`, then only checks that the auth store's
    revision is unchanged (`v3_server.go:716-720`).
  - `checkLeaseTimeToLive` (`v3_server.go:607-633`): for a non-admin user, looks the lease up in
    the **local** lessor and requires `IsRangePermitted` on every key it holds then.
  - `leaseTimeToLive` (`v3_server.go:636-668`): on the leader, after `waitAppliedIndex`, looks the
    lease up **again** (`v3_server.go:645`) and returns `le.Keys()` (`v3_server.go:651-657`); on a
    follower, forwards to the leader over leasehttp (`v3_server.go:670-690`), whose handler
    (`server/lease/leasehttp/http.go:109-150`) looks the lease up in the leader's lessor and
    returns its keys.
  - What lets another user attach a key in between: `apply/auth.go:198-220`
    (`checkLeasePuts`): a put with a lease requires write permission on the key and on the keys
    the lease already holds, nothing about who may read the lease's keys.
- **What happens**: user U may read `a` only; lease L holds `a`. U calls
  `TimeToLive(L, WithAttachedKeys())`. `checkLeaseTimeToLive` sees `{a}` and passes. Before the
  second lookup, root (or any user V who may write `a` and `b`) puts `b` with lease L. The second
  lookup returns `{a, b}`; the auth revision did not change (no auth operation), so the response
  carries `b`, a key name U may not read (U's `Get("b")` is refused with permission denied).
  The window is the time between the two lookups: on the leader it includes `waitAppliedIndex`;
  on a follower, the forward to the leader.

  **Follower variant.** On a follower the check and the answer read two different lessors: the
  check reads the follower's own lessor, which has applied up to the follower's applied index
  (`checkLeaseTimeToLive` does not wait for any index), and the keys come from the leader's lessor
  after it has applied everything it committed. So even without a concurrent put during the
  request, a follower that lags behind the leader passes the check on its stale key set while the
  leader returns a newer one: any key attached to L that the follower has not applied yet leaks.
  The window there is as long as the follower's apply lag, not just a few instructions.

  Reproduction: `tests/integration/v3_lease_ttl_keys_toctou_test.go`, with gofail enabled in
  `server/etcdserver` and `server/lease/leasehttp` (from the etcd root at 249d76bea:
  `gofail enable server/etcdserver/ server/lease/leasehttp/ && (cd server && go get
  go.etcd.io/gofail@v0.2.0)`, then `cd tests && go test ./integration/ -run
  TestV3LeaseTimeToLiveKeysTOCTOU -v`). The leader case sleeps at the existing failpoint
  `beforeLookupWhenLeaseTimeToLive` (between the check and the second lookup, on a single-member
  cluster); the follower case (3 members, U's client on a follower) sleeps at
  `beforeLookupWhenForwardLeaseTimeToLive` in the leader's leasehttp handler. Both fail:

  ```
  v3_lease_ttl_keys_toctou_test.go:122: keys returned to u: [a b]
      Error:      	[]string{"a", "b"} should not contain "b"
      Test:       	TestV3LeaseTimeToLiveKeysTOCTOU/leader
      Messages:   	LeaseTimeToLive returned a key the caller may not read
  ...
  v3_lease_ttl_keys_toctou_test.go:122: keys returned to u: [a b]
      Test:       	TestV3LeaseTimeToLiveKeysTOCTOU/follower
  --- FAIL: TestV3LeaseTimeToLiveKeysTOCTOU (4.28s)
      --- FAIL: TestV3LeaseTimeToLiveKeysTOCTOU/leader (2.09s)
      --- FAIL: TestV3LeaseTimeToLiveKeysTOCTOU/follower (2.19s)
  ```

  The failpoints only widen the window; the race itself needs no failpoint (the follower lag
  variant needs no concurrency within the request at all). Not measured without gofail.

  ```go
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
  ```
- **Expected**: the keys returned are the keys whose read permission was checked: `LeaseTimeToLive`
  with `Keys` returns a key only to a user who may read it (as the check intends: "check RBAC
  permission only if Keys is true", `v3_server.go:706`).
- **How the proof handles it**: no verified result covers `LeaseTimeToLive` (only its callee
  `EtcdServer.requireAuthInfo` has a spec, `Spec/go_etcd_io/etcd/server/v3/etcdserver/
  EtcdServer__requireAuthInfo.lean`). Found by code reading while looking at the lease keys.
- **Possible fixes**: check permission on the keys actually returned, after the lookup that
  produces them: in `LeaseTimeToLive`, after `leaseTimeToLive` returns, run `IsRangePermitted` on
  each of `resp.Keys` (and keep the revision re-check, or check against the auth info at that
  revision); this covers the leader and the follower paths alike, since the follower then checks
  the leader's key set. Alternatively filter `resp.Keys` to the readable ones, though refusing
  matches the current semantics (the whole request fails if any key is unreadable).
- **Found**: 2026-10-31, by code reading (`LeaseTimeToLive`'s two lookups), confirmed by the
  integration test above.
