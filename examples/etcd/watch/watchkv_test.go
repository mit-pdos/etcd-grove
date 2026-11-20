package watch

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative), 4 writers of 25 Puts each; the check must pass. Then it asks the member Main left
// running whether the Puts took effect (so that the check was not vacuous).
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.Reset(t, "watchkv") // the members' WAL areas (wal-link P2)
	if r := Main(4, 25); r != Ok {
		t.Fatalf("got %v", r)
	}

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, prefix, clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	if resp.Header.Revision != 101 {
		t.Fatalf("Main's Puts did not all take effect: revision %d", resp.Header.Revision)
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}
