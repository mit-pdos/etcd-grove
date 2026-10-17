package concurrency_test

import (
	"context"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// reviewWatcher passes watches on the prefix through to the wrapped Watcher,
// except the n-th one (1-based) and later, which fail with a compacted error
// after running hook (if any).
type reviewWatcher struct {
	clientv3.Watcher
	prefix string
	failAt int32
	count  atomic.Int32
	hook   func()
}

func (w *reviewWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	if strings.HasPrefix(key, w.prefix) && w.count.Add(1) >= w.failAt {
		if w.hook != nil {
			w.hook()
		}
		ch := make(chan clientv3.WatchResponse, 1)
		ch <- clientv3.WatchResponse{CompactRevision: 1}
		close(ch)
		return ch
	}
	return w.Watcher.Watch(ctx, key, opts...)
}

// R1: waitDeletes fails (compacted) and then the server becomes unreachable.
// Before the PR, Campaign returned the error at once (ctx not done). With the
// PR, Campaign runs Resign(client.Ctx()), which waits for the connection with a
// context that is never canceled: Campaign outlives the caller's deadline and
// returns only once the server is back.
func TestReviewCampaignCleanupIgnoresCallerDeadline(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	const prefix = "/review-deadline/"
	m := clus.Members[0]

	cli1, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{m.GRPCURL}})
	require.NoError(t, err)
	defer cli1.Close()
	s1, err := concurrency.NewSession(cli1)
	require.NoError(t, err)
	defer s1.Close()
	require.NoError(t, concurrency.NewElection(s1, prefix).Campaign(t.Context(), "candidate1"))

	cli2, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{m.GRPCURL}})
	require.NoError(t, err)
	defer cli2.Close()
	s2, err := concurrency.NewSession(cli2)
	require.NoError(t, err)
	defer s2.Close()
	stopped := make(chan time.Time, 1)
	cli2.Watcher = &reviewWatcher{Watcher: cli2.Watcher, prefix: prefix, failAt: 1,
		hook: func() { m.Stop(t); stopped <- time.Now() }}
	e2 := concurrency.NewElection(s2, prefix)

	// The caller's context: canceled 2s after the server is down.
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	done := make(chan error, 1)
	go func() { done <- e2.Campaign(ctx, "candidate2") }()
	start := <-stopped
	t.Logf("server stopped; waitDeletes now fails with a compacted error")
	time.AfterFunc(2*time.Second, cancel)

	var cerr error
	returned := false
	select {
	case cerr = <-done:
		returned = true
	case <-time.After(6 * time.Second):
	}
	t.Logf("Campaign returned within 6s (caller ctx canceled at 2s): %v; elapsed %v; err %v",
		returned, time.Since(start), cerr)
	require.NoError(t, m.Restart(t))
	if !returned {
		select {
		case cerr = <-done:
			t.Logf("Campaign returned after the server restarted: elapsed %v; err %v", time.Since(start), cerr)
		case <-time.After(30 * time.Second):
			t.Logf("Campaign still blocked 30s after restart")
		}
	}
	require.Truef(t, returned, "Campaign blocked past the caller's cancel while the server was down")
}

// R2: two Elections on the same session and prefix share one key. With the PR,
// a non-context failure of one Campaign's wait deletes the shared key while the
// other Campaign waits on it; that Campaign then returns nil without a key, at
// the same time as a third candidate becomes the real leader.
func TestReviewCampaignCleanupDeletesSharedKey(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	const prefix = "/review-shared/"
	ep := []string{clus.Members[0].GRPCURL}

	cli0, err := integration.NewClient(t, clientv3.Config{Endpoints: ep})
	require.NoError(t, err)
	defer cli0.Close()
	s0, err := concurrency.NewSession(cli0)
	require.NoError(t, err)
	defer s0.Close()
	e0 := concurrency.NewElection(s0, prefix)
	require.NoError(t, e0.Campaign(t.Context(), "leader0"))

	cli1, err := integration.NewClient(t, clientv3.Config{Endpoints: ep})
	require.NoError(t, err)
	defer cli1.Close()
	w := &reviewWatcher{Watcher: cli1.Watcher, prefix: prefix, failAt: 2}
	cli1.Watcher = w
	s1, err := concurrency.NewSession(cli1)
	require.NoError(t, err)
	defer s1.Close()

	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	var wg sync.WaitGroup
	defer wg.Wait()

	e1 := concurrency.NewElection(s1, prefix)
	e1done := make(chan error, 1)
	wg.Add(1)
	go func() { defer wg.Done(); e1done <- e1.Campaign(ctx, "v") }()
	require.Eventually(t, func() bool { return w.count.Load() == 1 }, 5*time.Second, 10*time.Millisecond)

	// A third candidate, queued behind e1.
	s3, err := concurrency.NewSession(cli0)
	require.NoError(t, err)
	defer s3.Close()
	e3 := concurrency.NewElection(s3, prefix)
	e3done := make(chan error, 1)
	wg.Add(1)
	go func() { defer wg.Done(); e3done <- e3.Campaign(ctx, "candidate3") }()
	time.Sleep(500 * time.Millisecond)

	// e2: same session and prefix as e1, so the same key; its wait fails (compacted).
	e2 := concurrency.NewElection(s1, prefix)
	err = e2.Campaign(ctx, "v")
	t.Logf("e2.Campaign: %v", err)
	require.Error(t, err)

	key := e1.Key()
	resp, err := cli0.Get(t.Context(), key)
	require.NoError(t, err)
	t.Logf("after e2's failed Campaign, the shared key %q exists: %v", key, len(resp.Kvs) == 1)

	require.NoError(t, e0.Resign(t.Context()))
	var e1err, e3err error
	e1ok, e3ok := false, false
	timeout := time.After(3 * time.Second)
	for !(e1ok && e3ok) {
		select {
		case e1err = <-e1done:
			e1ok = true
		case e3err = <-e3done:
			e3ok = true
		case <-timeout:
			goto out
		}
	}
out:
	resp, err = cli0.Get(t.Context(), key)
	require.NoError(t, err)
	t.Logf("e1.Campaign returned: %v (err %v), its key exists: %v", e1ok, e1err, len(resp.Kvs) == 1)
	t.Logf("e3.Campaign returned: %v (err %v)", e3ok, e3err)
	cancel()
	bothLeaders := e1ok && e1err == nil && e3ok && e3err == nil
	require.Falsef(t, bothLeaders, "e1 and e3 both won the election")
}
