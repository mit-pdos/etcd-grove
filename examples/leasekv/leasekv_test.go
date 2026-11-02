package leasekv

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative); the checks must pass. Then, on the member Main left running, it checks the answers
// Main saw are the empty lessor's (TimeToLive's TTL -1, no lease listed), grants a lease and checks
// the answers about it.
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
	ttl0, err := cli.TimeToLive(ctx, leaseID)
	if err != nil || ttl0.TTL != -1 || ttl0.ID != leaseID {
		t.Fatalf("TimeToLive of an absent lease: %v %v", ttl0, err)
	}
	g, err := cli.Grant(ctx, 60)
	if err != nil {
		t.Fatal(err)
	}
	ttl, err := cli.TimeToLive(ctx, g.ID)
	if err != nil {
		t.Fatal(err)
	}
	if ttl.TTL <= 0 || ttl.ID != g.ID {
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
