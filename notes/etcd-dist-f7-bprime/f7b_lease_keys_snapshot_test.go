// F7 (b') check (2026-11-26): is LeaseTimeToLive with keys either refused, or its reply free of
// keys the caller may not read, on a follower applying a snapshot?
//
// A three-member cluster, auth on. u may read "a/" only. root's lease Lz holds "z/lease". u's
// client is on a follower F. F is partitioned while the leader writes past its raft log's
// compaction, so on healing F receives and applies a snapshot. The test-only failpoint
// applyAfterRecoverLessor (added after lessor.Recover in applySnapshot, before mvcc's Restore
// re-attaches the keys) only widens the window. u's TimeToLive(Lz, keys) at F passes F's check
// over Lz's empty key set and is forwarded to the leader, whose lessor answers with "z/lease".
package integration

import (
	"context"
	"errors"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	gofail "go.etcd.io/gofail/runtime"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestF7bLeaseKeysAfterSnapshot(t *testing.T) {
	integration.SkipIfNoGoFail(t)
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, SnapshotCount: 10, SnapshotCatchUpEntries: 5})
	defer clus.Terminate(t)

	leadIdx := clus.WaitLeader(t)
	fIdx := (leadIdx + 1) % 3

	authSetupRoot(t, integration.ToGRPC(clus.Client(leadIdx)).Auth)
	rootc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(leadIdx).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootc.Close()

	ctx, cancel := context.WithTimeout(t.Context(), 60*time.Second)
	defer cancel()

	_, err = rootc.UserAdd(ctx, "u", "u-pw")
	require.NoError(t, err)
	_, err = rootc.RoleAdd(ctx, "ra")
	require.NoError(t, err)
	_, err = rootc.RoleGrantPermission(ctx, "ra", "a/", clientv3.GetPrefixRangeEnd("a/"), clientv3.PermissionType(clientv3.PermReadWrite))
	require.NoError(t, err)
	_, err = rootc.UserGrantRole(ctx, "u", "ra")
	require.NoError(t, err)

	lz, err := rootc.Grant(ctx, 9000)
	require.NoError(t, err)
	_, err = rootc.Put(ctx, "z/lease", "v", clientv3.WithLease(lz.ID))
	require.NoError(t, err)

	uc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(fIdx).Endpoints(), Username: "u", Password: "u-pw"})
	require.NoError(t, err)
	defer uc.Close()

	// Before: F holds Lz with z/lease, so u is refused (wait until F has applied the put).
	require.Eventually(t, func() bool {
		_, e := uc.TimeToLive(ctx, lz.ID, clientv3.WithAttachedKeys())
		return e != nil
	}, 10*time.Second, 50*time.Millisecond)
	_, err = uc.Get(ctx, "z/lease")
	require.Error(t, err, "u may not read z/lease")

	require.NoError(t, gofail.Enable("applyAfterRecoverLessor", `sleep("3s")`))
	t.Cleanup(func() {
		if terr := gofail.Disable("applyAfterRecoverLessor"); terr != nil && !errors.Is(terr, gofail.ErrDisabled) {
			t.Errorf("disable: %v", terr)
		}
	})

	// Partition F, write past the leader's log compaction, heal: F gets a snapshot.
	f := clus.Members[fIdx]
	others := []*integration.Member{}
	for i, m := range clus.Members {
		if i != fIdx {
			others = append(others, m)
		}
	}
	f.InjectPartition(t, others...)
	for i := 0; i < 60; i++ {
		_, err = rootc.Put(ctx, fmt.Sprintf("p/%d", i), "v")
		require.NoError(t, err)
	}
	f.RecoverPartition(t, others...)

	// u calls TimeToLive with keys at F until one is not refused.
	deadline := time.Now().Add(20 * time.Second)
	var leaked []string
	passed := false
	for time.Now().Before(deadline) {
		cctx, ccancel := context.WithTimeout(ctx, 2*time.Second)
		r, e := uc.TimeToLive(cctx, lz.ID, clientv3.WithAttachedKeys())
		ccancel()
		if e == nil {
			passed = true
			for _, k := range r.Keys {
				leaked = append(leaked, string(k))
			}
			t.Logf("u's TimeToLive(Lz, keys) at F was not refused; keys: %v", leaked)
			break
		}
		time.Sleep(20 * time.Millisecond)
	}
	require.True(t, passed, "u's TimeToLive at F was always refused (window not hit)")
	require.NotContains(t, leaked, "z/lease", "(b') false: the reply discloses a key u may not read")
}
