package concurrency_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/concurrency"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// Probe 1: a restarted process with the surviving lease gets its lock back with Lock().
func TestProbeResumeViaLock(t *testing.T) {
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	s1, err := concurrency.NewSession(cli)
	require.NoError(t, err)
	defer s1.Close()
	m1 := concurrency.NewMutex(s1, "/probe1")
	require.NoError(t, m1.Lock(t.Context()))
	g, _ := cli.Get(t.Context(), m1.Key())
	rev := g.Kvs[0].CreateRevision
	_, err = cli.Put(t.Context(), "/unrelated", "x") // any later write
	require.NoError(t, err)
	// "restart": a new session on the same lease
	s2, err := concurrency.NewSession(cli, concurrency.WithLease(s1.Lease()))
	require.NoError(t, err)
	m2 := concurrency.NewMutex(s2, "/probe1")
	require.NoError(t, m2.TryLock(t.Context())) // non-blocking, does not delete when owned
	require.Equal(t, m1.Key(), m2.Key())
	tr, err := cli.Txn(t.Context()).If(m2.IsOwner()).Commit()
	require.NoError(t, err)
	require.True(t, tr.Succeeded)
	t.Logf("create rev %d, m2.Header().Revision %d (Else branch)", rev, m2.Header().Revision)
	require.NotEqual(t, rev, m2.Header().Revision, "Header().Revision is not myRev on the reuse path")
}

// Probe 2: Header().Revision != create revision after a waiting Lock.
func TestProbeHeaderRevAfterWait(t *testing.T) {
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	sa, _ := concurrency.NewSession(cli)
	defer sa.Close()
	sb, _ := concurrency.NewSession(cli)
	defer sb.Close()
	ma := concurrency.NewMutex(sa, "/probe2")
	require.NoError(t, ma.Lock(t.Context()))
	mb := concurrency.NewMutex(sb, "/probe2")
	done := make(chan error)
	go func() { done <- mb.Lock(t.Context()) }()
	for {
		g, _ := cli.Get(t.Context(), "/probe2/", clientv3.WithPrefix())
		if len(g.Kvs) == 2 {
			break
		}
	}
	require.NoError(t, ma.Unlock(t.Context()))
	require.NoError(t, <-done)
	g, _ := cli.Get(t.Context(), mb.Key())
	t.Logf("create rev %d, Header().Revision %d (wait path)", g.Kvs[0].CreateRevision, mb.Header().Revision)
	require.NotEqual(t, g.Kvs[0].CreateRevision, mb.Header().Revision)
}

// Probe 3: a resumed mutex with a stale (key, rev) — the key was released and re-created by
// another handle of the same lease — has IsOwner false but Unlock still deletes the new key,
// releasing the lock the other handle holds.
func TestProbeResumedStaleUnlockDeletesRecreated(t *testing.T) {
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	s, _ := concurrency.NewSession(cli)
	defer s.Close()
	m1 := concurrency.NewMutex(s, "/probe3")
	require.NoError(t, m1.Lock(t.Context()))
	key := m1.Key()
	g, _ := cli.Get(t.Context(), key)
	staleRev := g.Kvs[0].CreateRevision
	require.NoError(t, m1.Unlock(t.Context()))
	m3 := concurrency.NewMutex(s, "/probe3")
	require.NoError(t, m3.Lock(t.Context())) // re-creates the same key
	stale := concurrency.ResumeMutex(s, "/probe3", key, staleRev)
	tr, _ := cli.Txn(t.Context()).If(stale.IsOwner()).Commit()
	require.False(t, tr.Succeeded, "IsOwner fences the stale handle")
	require.NoError(t, stale.Unlock(t.Context()), "Unlock does not")
	g, _ = cli.Get(t.Context(), key)
	require.Empty(t, g.Kvs, "the stale handle deleted m3's lock key")
}

// Probe 4: a resumed mutex given another session's key: Unlock deletes it (no ownership check).
func TestProbeResumedForeignKeyUnlock(t *testing.T) {
	cli, err := integration.NewClient(t, clientv3.Config{Endpoints: exampleEndpoints()})
	require.NoError(t, err)
	defer cli.Close()
	sa, _ := concurrency.NewSession(cli)
	defer sa.Close()
	sb, _ := concurrency.NewSession(cli)
	defer sb.Close()
	ma := concurrency.NewMutex(sa, "/probe4")
	require.NoError(t, ma.Lock(t.Context()))
	g, _ := cli.Get(t.Context(), ma.Key())
	mb := concurrency.ResumeMutex(sb, "/probe4", ma.Key(), g.Kvs[0].CreateRevision)
	require.NoError(t, mb.Unlock(t.Context()))
	g, _ = cli.Get(t.Context(), ma.Key())
	require.Empty(t, g.Kvs, "session B's resumed handle deleted session A's lock key")
	// and a resumed handle's Header() is nil until Lock
	require.Nil(t, concurrency.ResumeMutex(sb, "/probe4", "k", 1).Header())
}
