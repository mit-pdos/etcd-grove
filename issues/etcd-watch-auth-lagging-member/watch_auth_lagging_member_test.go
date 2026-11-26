package integration

import (
	"context"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestWatchAuthLaggingMember: a member that has not yet applied AuthEnable accepts an
// unauthenticated watch, and once it catches up the watch delivers keys written after auth was
// enabled, to a client that has no credentials.
//
// A follower is cut off from the other two members; auth is enabled through them and root writes
// keys under c/. An anonymous client then watches c/ at the follower, which checks the create
// against its own state (auth still off) and accepts it. The partition is healed: the follower
// applies AuthEnable and root's writes, and the anonymous watch receives every one of them.
func TestWatchAuthLaggingMember(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)
	ctx := context.Background()
	newCli := func(m *integration.Member, user, pw string) *clientv3.Client {
		c, err := clientv3.New(clientv3.Config{Endpoints: []string{m.GRPCURL}, Username: user, Password: pw,
			DialTimeout: 5 * time.Second, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		return c
	}

	lead := clus.WaitLeader(t)
	f := clus.Members[(lead+1)%3]
	var others []*integration.Member
	for _, m := range clus.Members {
		if m != f {
			others = append(others, m)
		}
	}
	l := clus.Members[lead]

	anonL := newCli(l, "", "")
	defer anonL.Close()
	if _, err := anonL.Put(ctx, "c/0", "before"); err != nil {
		t.Fatal(err)
	}
	// let the follower apply it, then cut it off
	anonF := newCli(f, "", "")
	defer anonF.Close()
	if _, err := anonF.Get(ctx, "c/0"); err != nil {
		t.Fatal(err)
	}
	f.InjectPartition(t, others...)

	// enable auth through the majority, and write as root
	for _, step := range []func() error{
		func() error { _, err := anonL.UserAdd(ctx, "root", "root-pw"); return err },
		func() error { _, err := anonL.UserGrantRole(ctx, "root", "root"); return err },
		func() error { _, err := anonL.AuthEnable(ctx); return err },
	} {
		if err := step(); err != nil {
			t.Fatal(err)
		}
	}
	root := newCli(l, "root", "root-pw")
	defer root.Close()
	const n = 10
	for i := 0; i < n; i++ {
		if _, err := root.Put(ctx, "c/after"+string(rune('0'+i)), "secret"); err != nil {
			t.Fatal(err)
		}
	}
	// at the leader, an anonymous watch is refused
	lctx, lcancel := context.WithTimeout(ctx, 3*time.Second)
	for r := range anonL.Watch(lctx, "c/", clientv3.WithPrefix(), clientv3.WithRev(1)) {
		if len(r.Events) > 0 {
			t.Fatalf("the leader served an anonymous watch: %v", r.Events)
		}
		if r.Canceled {
			t.Logf("at the leader: anonymous watch refused: %v", r.Err())
			break
		}
	}
	lcancel()

	// at the follower, still cut off: the anonymous watch is accepted
	wctx, wcancel := context.WithTimeout(ctx, 20*time.Second)
	defer wcancel()
	wch := anonF.Watch(wctx, "c/", clientv3.WithPrefix(), clientv3.WithRev(1))
	r := <-wch
	if r.Canceled || len(r.Events) == 0 {
		t.Fatalf("the follower refused the anonymous watch before it caught up: %v", r.Err())
	}
	t.Logf("at the cut-off follower: anonymous watch accepted, first response %d event(s)", len(r.Events))

	f.RecoverPartition(t, others...)
	var after []string
	for len(after) < n {
		r, ok := <-wch
		if !ok {
			break
		}
		for _, e := range r.Events {
			if strings.HasPrefix(string(e.Kv.Key), "c/after") {
				after = append(after, string(e.Kv.Key))
			}
		}
		if r.Canceled {
			break
		}
	}
	if len(after) > 0 {
		t.Fatalf("a watch without credentials received %d keys written after AuthEnable: %v", len(after), after)
	}
}
