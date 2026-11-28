package txnlin

import (
	"context"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// TestMainRun runs Main for real: one member in a fresh data directory, 8 clients of 100
// operations each, and porcupine's verdict must be Ok; then it checks that writes took effect.
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.Reset(t, "linkvtxn") // the members' WAL areas (wal-link P2)
	if r := Main(8, 100); r != porcupine.Ok {
		t.Fatalf("got %v", r)
	}
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	resp, err := cli.Get(ctx, "k", clientv3.WithPrefix())
	if err != nil {
		t.Fatal(err)
	}
	if resp.Header.Revision < 20 {
		t.Fatalf("Main's writes did not take effect: revision %d", resp.Header.Revision)
	}
	t.Logf("revision %d after Main, keys %d", resp.Header.Revision, len(resp.Kvs))
}
