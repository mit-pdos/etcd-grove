package compactkv

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestCompactKV runs Main once, in a fresh data directory (the member's DataDir is relative). Main
// returns without its checks if a step fails, so the test then asks the member Main left running
// whether the last round took effect, and whether the compactions did: a read at the first round's
// revision must fail with ErrCompacted (the last round compacted past it).
func TestCompactKV(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	keys := []string{"k1", "k2", "k3", "k4", "k5"}
	if len(keys) != rounds {
		t.Fatalf("the test's keys are not Main's rounds")
	}
	for _, k := range keys {
		r, err := cli.Get(ctx, k)
		if err != nil {
			t.Fatal(err)
		}
		if len(r.Kvs) != 1 || string(r.Kvs[0].Value) != value {
			t.Fatalf("Main's Put of %s did not take effect: %v", k, r.Kvs)
		}
	}
	last := keys[len(keys)-1]
	resp, err := cli.Get(ctx, last)
	if err != nil {
		t.Fatal(err)
	}
	// The rounds wrote at revisions 2, 3, ...: the store's revision is 1 + rounds, and the last
	// round compacted at the revision before it.
	if got, want := resp.Header.Revision, int64(1+rounds); got != want {
		t.Fatalf("store revision %d, want %d", got, want)
	}
	// keys[0]'s write (revision 2) is below the last compaction: reading there fails
	_, err = cli.Get(ctx, keys[0], clientv3.WithRev(2))
	if !errors.Is(err, rpctypes.ErrCompacted) {
		t.Fatalf("read at the first round's revision: %v, want ErrCompacted", err)
	}
	// the last compaction's revision still reads: the next-to-last round's key is there
	r, err := cli.Get(ctx, keys[len(keys)-2], clientv3.WithRev(resp.Header.Revision-1))
	if err != nil {
		t.Fatalf("read at the last compaction's revision: %v", err)
	}
	if len(r.Kvs) != 1 || string(r.Kvs[0].Value) != value {
		t.Fatalf("read at the last compaction's revision: %v", r.Kvs)
	}
	// the last round's key did not exist at that revision
	r, err = cli.Get(ctx, last, clientv3.WithRev(resp.Header.Revision-1))
	if err != nil || len(r.Kvs) != 0 {
		t.Fatalf("read of the last key before its round: %v, %v", r, err)
	}
	// a watch from revision 2, below the compactions, ends with ErrCompacted (as Main's)
	wctx, wcancel := context.WithCancel(context.Background())
	defer wcancel()
	wresp := <-cli.Watch(wctx, last, clientv3.WithRev(2))
	if !errors.Is(wresp.Err(), rpctypes.ErrCompacted) || wresp.CompactRevision == 0 {
		t.Fatalf("watch from revision 2: %v (compact revision %d), want ErrCompacted",
			wresp.Err(), wresp.CompactRevision)
	}
	// Main's C3 check is tight: the compaction revision plus the retention is the latest revision
	// (the last round compacted at the revision before its Put's)
	if wresp.CompactRevision+retention != resp.Header.Revision {
		t.Fatalf("compaction revision %d plus the retention %d, want the latest revision %d",
			wresp.CompactRevision, retention, resp.Header.Revision)
	}
}
