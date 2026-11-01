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
	resp, err := cli.Get(ctx, key)
	if err != nil {
		t.Fatal(err)
	}
	last := values[len(values)-1]
	if len(resp.Kvs) != 1 || string(resp.Kvs[0].Value) != last {
		t.Fatalf("Main's last Put did not take effect: %v", resp.Kvs)
	}
	// The rounds wrote at revisions 2, 3, ...: the store's revision is 1 + len(values), and the
	// last round compacted at the revision before it.
	if got, want := resp.Header.Revision, int64(1+len(values)); got != want {
		t.Fatalf("store revision %d, want %d", got, want)
	}
	_, err = cli.Get(ctx, key, clientv3.WithRev(2))
	if !errors.Is(err, rpctypes.ErrCompacted) {
		t.Fatalf("read at the first round's revision: %v, want ErrCompacted", err)
	}
	// The latest compaction is at the revision before the last write.
	_, err = cli.Get(ctx, key, clientv3.WithRev(resp.Header.Revision-2))
	if !errors.Is(err, rpctypes.ErrCompacted) {
		t.Fatalf("read below the last compaction: %v, want ErrCompacted", err)
	}
	r, err := cli.Get(ctx, key, clientv3.WithRev(resp.Header.Revision-1))
	if err != nil {
		t.Fatalf("read at the last compaction's revision: %v", err)
	}
	if len(r.Kvs) != 1 || string(r.Kvs[0].Value) != values[len(values)-2] {
		t.Fatalf("read at the last compaction's revision: %v, want %s", r.Kvs, values[len(values)-2])
	}
}
