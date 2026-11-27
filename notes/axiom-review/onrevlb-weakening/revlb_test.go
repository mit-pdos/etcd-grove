package revlbtest

import (
	"context"
	"errors"
	"net/url"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/embed"
)

// Auth-on scenario: A (no write on x) puts x (denied at apply), then B runs k txns
// "if version(x)=0 then put y else {}", then B puts z. Prints each reply revision.
func TestDeniedPutRevision(t *testing.T) {
	cfg := embed.NewConfig()
	cfg.Dir = t.TempDir()
	cu, _ := url.Parse("http://127.0.0.1:23791")
	pu, _ := url.Parse("http://127.0.0.1:23801")
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = []url.URL{*cu}, []url.URL{*cu}
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = []url.URL{*pu}, []url.URL{*pu}
	cfg.InitialCluster = cfg.Name + "=" + pu.String()
	cfg.LogLevel = "error"
	e, err := embed.StartEtcd(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer e.Close()
	<-e.Server.ReadyNotify()
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	mk := func(u, p string) *clientv3.Client {
		c, err := clientv3.New(clientv3.Config{Endpoints: []string{cu.String()}, Username: u, Password: p})
		if err != nil {
			t.Fatal(err)
		}
		return c
	}
	root := mk("", "")
	must := func(_ any, err error) {
		if err != nil {
			t.Fatal(err)
		}
	}
	must(root.UserAdd(ctx, "root", "rootpw"))
	must(root.UserGrantRole(ctx, "root", "root"))
	must(root.RoleAdd(ctx, "rb"))
	must(root.RoleGrantPermission(ctx, "rb", "x", "", clientv3.PermissionType(clientv3.PermRead)))
	must(root.RoleGrantPermission(ctx, "rb", "y", "", clientv3.PermissionType(clientv3.PermReadWrite)))
	must(root.RoleGrantPermission(ctx, "rb", "z", "", clientv3.PermissionType(clientv3.PermReadWrite)))
	must(root.UserAdd(ctx, "a", "apw"))
	must(root.UserAdd(ctx, "b", "bpw"))
	must(root.UserGrantRole(ctx, "b", "rb"))
	must(root.AuthEnable(ctx))
	root.Close()
	ra := mk("root", "rootpw")
	g, err := ra.Get(ctx, "x")
	must(nil, err)
	r0 := g.Header.Revision
	t.Logf("start revision r0=%d (x absent: %v)", r0, len(g.Kvs) == 0)

	a, b := mk("a", "apw"), mk("b", "bpw")
	_, err = a.Put(ctx, "x", "1")
	t.Logf("A put x: err=%v", err)
	if !errors.Is(err, rpctypes.ErrPermissionDenied) {
		t.Fatalf("expected permission denied, got %v", err)
	}
	const k = 3
	for i := 0; i < k; i++ {
		tr, err := b.Txn(ctx).If(clientv3.Compare(clientv3.Version("x"), "=", 0)).
			Then(clientv3.OpPut("y", "v")).Commit()
		must(nil, err)
		t.Logf("B txn %d: succeeded=%v rev=%d", i, tr.Succeeded, tr.Header.Revision)
	}
	pr, err := b.Put(ctx, "z", "v")
	must(nil, err)
	t.Logf("B put z: rev=%d", pr.Header.Revision)
	g, err = ra.Get(ctx, "x")
	must(nil, err)
	t.Logf("x present after: %v; final rev %d", len(g.Kvs) != 0, g.Header.Revision)
	// kvModel (auth layer passes everything): start length r0+1; A's put +1; txns see x
	// (version 1) -> else {} -> +0; B put +1 => length r0+3.
	kvModelLen := r0 + 3
	if pr.Header.Revision >= kvModelLen {
		t.Logf("VIOLATION: reply rev %d >= kvModel length %d (kvRevLb needs rev < length)", pr.Header.Revision, kvModelLen)
	}
}
