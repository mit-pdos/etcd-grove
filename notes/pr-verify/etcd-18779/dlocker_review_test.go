// Review probes for etcd#18779 (DLocker / Mutex.Rev).

package concurrency_test

import (
	"context"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"

	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// Two DLockers on one session and prefix both hold the lock at once, with
// equal Rev(): a `<` fence accepts both holders' writes.
func TestReviewSameSessionEqualTokens(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	s, err := concurrency.NewSession(clus.RandClient())
	require.NoError(t, err)
	defer s.Close()
	l1 := concurrency.NewDLocker(s, "/same")
	l2 := concurrency.NewDLocker(s, "/same")
	l1.Lock()
	done := make(chan struct{})
	go func() { l2.Lock(); close(done) }()
	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("l2.Lock blocked (exclusive)")
	}
	t.Logf("both hold: l1.Rev()=%d l2.Rev()=%d", l1.Rev(), l2.Rev())
	require.Equal(t, l1.Rev(), l2.Rev())
	l1.Unlock()
	// l2 still "holds" the lock but its key is gone; its Rev is unchanged.
	t.Logf("after l1.Unlock: l2.Rev()=%d", l2.Rev())
}

// One DLocker shared by two goroutines, as sync.Locker invites: the second
// Lock returns while the first goroutine holds it; when the first unlocks,
// the second's Rev() becomes -1. Run with -race to see Rev/Lock race.
func TestReviewSharedLockerGoroutines(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	s, err := concurrency.NewSession(clus.RandClient())
	require.NoError(t, err)
	defer s.Close()
	l := concurrency.NewDLocker(s, "/shared")
	l.Lock()
	rev1 := l.Rev()
	var wg sync.WaitGroup
	wg.Add(1)
	var rev2 int64
	go func() {
		defer wg.Done()
		l.Lock() // returns immediately: same session key
		rev2 = l.Rev()
	}()
	wg.Wait()
	t.Logf("goroutine 1 rev %d, goroutine 2 acquired too, rev %d", rev1, rev2)
	l.Unlock()
	t.Logf("after goroutine 1 Unlock, goroutine 2 sees Rev()=%d", l.Rev())
	require.Equal(t, int64(-1), l.Rev())
}

// Mutex.Lock returning ErrSessionExpired (lease revoked while waiting) leaves
// myRev at the stale create revision: Rev() > 0 though no lock is held.
func TestReviewSessionExpiredStaleRev(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.RandClient()
	sC, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer sC.Close()
	sA, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer sA.Close()
	mC := concurrency.NewMutex(sC, "/exp")
	require.NoError(t, mC.Lock(context.TODO()))
	mA := concurrency.NewMutex(sA, "/exp")
	ch := make(chan error, 1)
	go func() { ch <- mA.Lock(context.TODO()) }()
	require.Eventually(t, func() bool {
		r, err := cli.Get(context.TODO(), "/exp/", clientv3.WithPrefix())
		return err == nil && len(r.Kvs) == 2
	}, 5*time.Second, 10*time.Millisecond)
	_, err = cli.Revoke(context.TODO(), sA.Lease())
	require.NoError(t, err)
	require.NoError(t, mC.Unlock(context.TODO()))
	var lerr error
	select {
	case lerr = <-ch:
	case <-time.After(5 * time.Second):
		t.Fatal("Lock did not return")
	}
	t.Logf("Lock err=%v, Rev()=%d", lerr, mA.Rev())
	require.ErrorIs(t, lerr, concurrency.ErrSessionExpired)
	require.Greater(t, mA.Rev(), int64(0))
}
