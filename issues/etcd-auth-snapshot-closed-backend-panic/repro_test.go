// Reproduction of issues/etcd-auth-snapshot-closed-backend-panic.md.
//
// Copy into tests/integration/ of an etcd checkout at the pin (8a24be2a3) or upstream main and run
//
//	go test ./integration -run 'TestAuthStoreCheckOnClosedBackend|TestV3AuthReadDuringSnapshotInstall' -count=1 -v
//
// from tests/.
package integration

import (
	"context"
	"runtime"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/auth"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestAuthStoreCheckOnClosedBackend is the state applySnapshot leaves between `go oldbe.Close()`
// and `authStore.Recover(newbe)`: auth enabled, the auth store's backend closed. Each permission
// check the gRPC handlers run before (or without) going through raft panics (a nil *bolt.Tx in
// baseReadTx.UnsafeRange) instead of returning an error. (Each check gets a fresh store: the panic
// leaves the read tx's txMu locked, so a second check on the same backend would block.)
func TestAuthStoreCheckOnClosedBackend(t *testing.T) {
	checks := map[string]func(as auth.AuthStore, ai *auth.AuthInfo){
		"IsRangePermitted": func(as auth.AuthStore, ai *auth.AuthInfo) { _ = as.IsRangePermitted(ai, []byte("k"), nil) },
		"IsPutPermitted":   func(as auth.AuthStore, ai *auth.AuthInfo) { _ = as.IsPutPermitted(ai, []byte("k")) },
		"IsAdminPermitted": func(as auth.AuthStore, ai *auth.AuthInfo) { _ = as.IsAdminPermitted(ai) },
		"CheckPassword":    func(as auth.AuthStore, ai *auth.AuthInfo) { _, _ = as.CheckPassword("root", "123") },
	}
	for name, check := range checks {
		t.Run(name, func(t *testing.T) {
			lg := zaptest.NewLogger(t)
			be, _ := betesting.NewDefaultTmpBackend(t)
			tp, err := auth.NewTokenProvider(lg, "simple", func(uint64) <-chan struct{} {
				ch := make(chan struct{}, 1)
				ch <- struct{}{}
				return ch
			}, 5*time.Minute)
			require.NoError(t, err)
			as := auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), tp, bcrypt.MinCost)
			defer as.Close()

			_, err = as.RoleAdd(&pb.AuthRoleAddRequest{Name: "root"})
			require.NoError(t, err)
			_, err = as.UserAdd(&pb.AuthUserAddRequest{Name: "root", Password: "123"})
			require.NoError(t, err)
			_, err = as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "root", Role: "root"})
			require.NoError(t, err)
			require.NoError(t, as.AuthEnable())
			ai := &auth.AuthInfo{Username: "root", Revision: as.Revision()}
			require.Nil(t, recovered(func() { check(as, ai) }), "live backend") // fine

			require.NoError(t, be.Close()) // what `go oldbe.Close()` does to the auth store's backend

			r := recovered(func() { check(as, ai) })
			require.NotNil(t, r, "no panic on the closed backend")
			rerr, ok := r.(runtime.Error)
			require.Truef(t, ok, "panic %v is not a runtime error", r)
			require.Contains(t, rerr.Error(), "nil pointer dereference")
			t.Logf("%s on the closed backend: panic: %v", name, rerr)
		})
	}
}

// waitLeaderNoAuth is clus.WaitLeader without its Gets, which the members' unauthenticated
// clients cannot do once auth is enabled.
func waitLeaderNoAuth(t *testing.T, clus *integration.Cluster) int {
	for deadline := time.Now().Add(10 * time.Second); time.Now().Before(deadline); time.Sleep(10 * time.Millisecond) {
		lead := clus.Members[0].Server.Leader()
		agree := lead != 0
		for _, m := range clus.Members {
			agree = agree && m.Server.Leader() == lead
		}
		if !agree {
			continue
		}
		for i, m := range clus.Members {
			if m.Server.MemberID() == lead {
				return i
			}
		}
	}
	t.Fatal("no leader")
	return -1
}

func recovered(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

// TestV3AuthReadDuringSnapshotInstall: auth enabled; a follower is partitioned while the leader
// writes past its log retention, then healed, so it installs the leader's snapshot; meanwhile
// clients send it serializable Gets as root. A Get whose permission check runs after the old
// backend's Close has started and before authStore.Recover panics the member (and, the members
// being in the test process, the test binary).
func TestV3AuthReadDuringSnapshotInstall(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size: 3, SnapshotCount: 10, SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	authSetupRoot(t, integration.ToGRPC(clus.Client(0)).Auth)

	// One install per run: after sending a snapshot the leader pauses its log compaction for
	// releaseDelayAfterSnapshot (30 s), so a second round would catch up from the log. Repeat
	// with -count.
	const rounds = 1
	const readers = 32
	installs := 0
	var reads atomic.Int64
	for round := 0; round < rounds; round++ {
		lead := waitLeaderNoAuth(t, clus)
		f := (lead + 1) % 3
		fm := clus.Members[f]
		var others []*integration.Member
		for i, m := range clus.Members {
			if i != f {
				others = append(others, m)
			}
		}

		rootF, err := integration.NewClient(t, clientv3.Config{
			Endpoints: []string{fm.GRPCURL}, Username: "root", Password: "123"})
		require.NoError(t, err)
		rootL, err := integration.NewClient(t, clientv3.Config{
			Endpoints: []string{clus.Members[lead].GRPCURL}, Username: "root", Password: "123"})
		require.NoError(t, err)
		_, err = rootF.Get(t.Context(), "k", clientv3.WithSerializable()) // authenticates now
		require.NoError(t, err)

		oldBe := fm.Server.Backend()
		fm.InjectPartition(t, others...)
		for i := 0; i < 40; i++ {
			_, err = rootL.Put(t.Context(), "k", "v")
			require.NoError(t, err)
		}

		ctx, cancel := context.WithCancel(t.Context())
		var wg sync.WaitGroup
		for r := 0; r < readers; r++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for ctx.Err() == nil {
					if _, gerr := rootF.Get(ctx, "k", clientv3.WithSerializable()); gerr == nil {
						reads.Add(1)
					}
				}
			}()
		}
		time.Sleep(50 * time.Millisecond)
		fm.RecoverPartition(t, others...)
		want := clus.Members[lead].Server.KV().Rev()
		deadline := time.Now().Add(10 * time.Second)
		for fm.Server.KV().Rev() < want && time.Now().Before(deadline) {
			time.Sleep(10 * time.Millisecond)
		}
		time.Sleep(100 * time.Millisecond)
		cancel()
		wg.Wait()
		require.GreaterOrEqual(t, fm.Server.KV().Rev(), want, "round %d: follower did not catch up", round)
		if fm.Server.Backend() != oldBe {
			installs++
		}
		rootF.Close()
		rootL.Close()
	}
	t.Logf("%d snapshot installs, %d reads, no panic", installs, reads.Load())
	require.Positive(t, installs, "no follower installed a snapshot")
}
