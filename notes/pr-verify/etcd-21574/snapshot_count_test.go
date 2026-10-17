// Probe for etcd-io/etcd#21574 (verification, not part of the PR).

package embed

import (
	"context"
	"fmt"
	"net/url"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage/wal"
)

// TestSnapshotCountRespected starts a single member with the default
// --snapshot-count (10000), writes 20 keys, and counts the snapshot records
// in its WAL. With 20 entries applied no disk snapshot is due.
func TestSnapshotCountRespected(t *testing.T) {
	cfg := NewConfig()
	// unix-socket URLs, as the package's own tests use (self-contained, so the
	// test runs on both the upstream PR head and the fork)
	var urls []url.URL
	for i := 0; i < 2; i++ {
		u, _ := url.Parse(fmt.Sprintf("unix://localhost:%d%06d", os.Getpid(), 7000+i))
		urls = append(urls, *u)
	}
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = urls[:1], urls[:1]
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = urls[1:], urls[1:]
	cfg.InitialCluster = "default=" + urls[1].String()
	cfg.Dir = t.TempDir()
	require.Equal(t, uint64(10000), cfg.SnapshotCount)

	e, err := StartEtcd(cfg)
	require.NoError(t, err)
	closed := false
	defer func() {
		if !closed {
			e.Close()
		}
	}()
	select {
	case <-e.Server.ReadyNotify():
	case <-time.After(10 * time.Second):
		t.Fatal("server not ready")
	}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	for i := 0; i < 20; i++ {
		_, err := e.Server.Put(ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte{byte(i)}})
		require.NoError(t, err)
	}

	// Stop the member so the WAL is complete, then count its snapshot records
	// (the bootstrap's index-0 record is one).
	e.Close()
	closed = true
	snaps, err := wal.ValidSnapshotEntries(zaptest.NewLogger(t), filepath.Join(cfg.Dir, "member", "wal"))
	require.NoError(t, err)
	t.Logf("WAL snapshot records after 20 puts with snapshot-count 10000: %d", len(snaps))
	require.LessOrEqual(t, len(snaps), 1, "disk snapshots were taken although snapshot-count was not reached")
}
