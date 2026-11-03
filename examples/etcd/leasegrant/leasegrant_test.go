package leasegrant

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative); its check must pass (no panic). Then, on the member Main left running, it checks that
// the lease Main granted is listed and lives.
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	ls, err := cli.Leases(ctx)
	if err != nil || len(ls.Leases) != 1 {
		t.Fatalf("Leases after Main: %v %v", ls, err)
	}
	ttl, err := cli.TimeToLive(ctx, ls.Leases[0].ID)
	if err != nil || ttl.TTL <= 0 || ttl.GrantedTTL != grantTTL {
		t.Fatalf("TimeToLive of the granted lease: %v %v", ttl, err)
	}
}
