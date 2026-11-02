package leasekv

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative); the checks must pass. Then it grants a lease on the member Main left running and asks
// TimeToLive of it (so that the check's TTL -1 is the answer for an absent lease, not every answer).
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	if r := Main(); r != Ok {
		t.Fatalf("got %v", r)
	}

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	g, err := cli.Grant(ctx, 60)
	if err != nil {
		t.Fatal(err)
	}
	ttl, err := cli.TimeToLive(ctx, g.ID)
	if err != nil {
		t.Fatal(err)
	}
	if ttl.TTL <= 0 {
		t.Fatalf("a granted lease's TTL is %d", ttl.TTL)
	}
	ls, err := cli.Leases(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if len(ls.Leases) != 1 {
		t.Fatalf("Leases after a grant: %d", len(ls.Leases))
	}
	t.Logf("granted %x, TTL %d", g.ID, ttl.TTL)
}
