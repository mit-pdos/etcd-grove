package etcdserver

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/pkg/v3/featuregate"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/etcd/server/v3/features"
)

// TestNewServerCheckpointerPropagatesRaftRequestError verifies that the lease
// Checkpointer closure installed by NewServer (server/etcdserver/server.go:398-407)
// propagates errors returned by srv.raftRequest instead of discarding them and
// returning nil (etcd-io/etcd#22650).
//
// When a lease has remainingTTL > 0 (set by an earlier checkpoint) and
// lessor.Renew calls the checkpointer to clear remainingTTL via Raft, a failed
// raftRequest must cause Renew to abort and return the error rather than
// refreshing the lease with the stale, shorter remainingTTL while returning the
// full nominal TTL to the caller.
func TestNewServerCheckpointerPropagatesRaftRequestError(t *testing.T) {
	peerURLs, err := types.NewURLs([]string{"http://127.0.0.1:0"})
	require.NoError(t, err)
	clientURLs, err := types.NewURLs([]string{"http://127.0.0.1:0"})
	require.NoError(t, err)
	urlsMap, err := types.NewURLsMap("node0=http://127.0.0.1:0")
	require.NoError(t, err)

	fg := features.NewDefaultServerFeatureGate("node0", zaptest.NewLogger(t))
	require.NoError(t, fg.(featuregate.MutableFeatureGate).SetFromMap(map[string]bool{
		string(features.LeaseCheckpoint): true,
	}))

	cfg := config.ServerConfig{
		Name:               "node0",
		DataDir:            t.TempDir(),
		ClientURLs:         clientURLs,
		PeerURLs:           peerURLs,
		InitialPeerURLsMap: urlsMap,
		NewCluster:         true,
		TickMs:             100,
		ElectionTicks:      10,
		MaxRequestBytes:    1572864,
		Logger:             zaptest.NewLogger(t),
		ServerFeatureGate:  fg,
	}

	srv, err := NewServer(cfg)
	require.NoError(t, err)
	defer func() {
		srv.r.transport.Stop()
		srv.kv.Close()
		srv.lessor.Stop()
		srv.be.Close()
	}()

	// Grant a 100s lease, checkpoint its remainingTTL to 20s, and promote the lessor.
	const (
		leaseID       = 1
		nominalTTL    = int64(100)
		checkpointTTL = int64(20)
	)
	l, err := srv.lessor.Grant(leaseID, nominalTTL)
	require.NoError(t, err)
	srv.lessor.Checkpoint(leaseID, checkpointTTL)
	srv.lessor.Promote(0)
	require.LessOrEqual(t, l.Remaining(), time.Duration(checkpointTTL)*time.Second)

	// Mark the server active so srv.ensureLeadership() returns true inside the
	// checkpointer closure, and force srv.raftRequest to fail with
	// errors.ErrTooManyRequests (committedIndex - appliedIndex > maxGapBetweenApplyAndCommitIndex).
	srv.r.latestTickTs = time.Now()
	srv.setCommittedIndex(maxGapBetweenApplyAndCommitIndex + 1)

	gotTTL, err := srv.lessor.Renew(leaseID)
	require.ErrorIs(t, err, errors.ErrTooManyRequests,
		"Renew must fail with the raftRequest error instead of swallowing it as nil; got ttl=%d, err=%v",
		gotTTL, err)
}
