package leaseexpiry

import (
	"context"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.uber.org/zap"
)

// TestMainRun runs Main for real: one member in a fresh data directory (Main's DataDir is
// relative); its check must pass (no panic). Then, on the member Main left running, it checks that
// the lease really expired: the listing is empty, and a grant made now expires as Main's did.
func TestMainRun(t *testing.T) {
	t.Chdir(t.TempDir())
	start := time.Now()
	Main()
	t.Logf("Main returned after %v", time.Since(start))

	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clientAddr}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	ls, err := cli.Leases(ctx)
	if err != nil || len(ls.Leases) != 0 {
		t.Fatalf("Leases after Main: %v %v (want none: Main's lease expired)", ls, err)
	}

	// The overdue answer: a lease past its TTL whose revocation is not yet applied answers TTL -1
	// with its GrantedTTL, which is why Main's not-found test also checks GrantedTTL = 0. Seen only
	// if a poll lands in that window; logged, not required.
	g, err := cli.Grant(ctx, grantTTL)
	if err != nil {
		t.Fatal(err)
	}
	sawOverdue, sawGone := false, false
	for i := 0; i < polls && !sawGone; i++ {
		time.Sleep(50 * time.Millisecond)
		r, err := cli.TimeToLive(ctx, g.ID)
		if err != nil {
			t.Fatal(err)
		}
		if r.TTL == -1 && r.GrantedTTL != 0 {
			sawOverdue = true
		}
		if r.TTL == -1 && r.GrantedTTL == 0 {
			sawGone = true
		}
	}
	if !sawGone {
		t.Fatalf("the second lease did not expire")
	}
	t.Logf("overdue answer seen: %v", sawOverdue)
}
