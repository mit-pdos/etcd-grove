package embed

import (
	"context"
	"net/url"
	"os"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	epb "go.etcd.io/etcd/server/v3/etcdserver/api/v3election/v3electionpb"
)

// Two users campaign concurrently through the server-side Election service, each on an
// election under its own prefix. user2's second Campaign must wait (its predecessor's lease
// is alive), not fail with "permission denied".
func TestIssue17502ElectionWrongIdentity(t *testing.T) {
	cfg := NewConfig()
	cfg.Dir = t.TempDir()
	cu, _ := url.Parse("http://127.0.0.1:23791")
	pu, _ := url.Parse("http://127.0.0.1:23801")
	cfg.ListenClientUrls, cfg.AdvertiseClientUrls = []url.URL{*cu}, []url.URL{*cu}
	cfg.ListenPeerUrls, cfg.AdvertisePeerUrls = []url.URL{*pu}, []url.URL{*pu}
	cfg.InitialCluster = cfg.InitialClusterFromName(cfg.Name)
	cfg.LogLevel = "error"
	e, err := StartEtcd(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer e.Close()
	<-e.Server.ReadyNotify()

	ep := []string{cu.String()}
	root, err := clientv3.New(clientv3.Config{Endpoints: ep})
	if err != nil {
		t.Fatal(err)
	}
	defer root.Close()
	ctx := context.Background()
	must := func(_ any, err error) {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
	}
	must(root.UserAdd(ctx, "root", "rootpw"))
	must(root.UserGrantRole(ctx, "root", "root"))
	for _, u := range []string{"u1", "u2"} {
		must(root.RoleAdd(ctx, "r"+u))
		must(root.RoleGrantPermission(ctx, "r"+u, u+"/", clientv3.GetPrefixRangeEnd(u+"/"), clientv3.PermissionType(clientv3.PermReadWrite)))
		must(root.UserAdd(ctx, u, u+"pw"))
		must(root.UserGrantRole(ctx, u, "r"+u))
	}
	must(root.AuthEnable(ctx))

	cl := func(u string) *clientv3.Client {
		c, err := clientv3.New(clientv3.Config{Endpoints: ep, Username: u, Password: u + "pw"})
		if err != nil {
			t.Fatal(err)
		}
		return c
	}
	c1, c2 := cl("u1"), cl("u2")
	defer c1.Close()
	defer c2.Close()
	campaign := func(c *clientv3.Client, name string, cctx context.Context) error {
		l, err := c.Grant(ctx, 60)
		if err != nil {
			return err
		}
		_, err = epb.NewElectionClient(c.ActiveConnection()).Campaign(cctx,
			&epb.CampaignRequest{Name: []byte(name), Lease: int64(l.ID), Value: []byte("v")})
		return err
	}

	// user1: leader, then a second campaign that waits (its waitDeletes watch opens the
	// in-process client's shared watch stream with user1's request context).
	if err := campaign(c1, "u1/e", ctx); err != nil {
		t.Fatal(err)
	}
	ctx1, cancel1 := context.WithCancel(ctx)
	defer cancel1()
	if os.Getenv("CONTROL") == "" {
		go campaign(c1, "u1/e", ctx1)
	}
	time.Sleep(time.Second)

	// user2: the same on its own election.
	if err := campaign(c2, "u2/e", ctx); err != nil {
		t.Fatal(err)
	}
	ctx2, cancel2 := context.WithTimeout(ctx, 3*time.Second)
	defer cancel2()
	err = campaign(c2, "u2/e", ctx2)
	if err == nil {
		t.Fatal("second campaign of u2 won while the first leader's lease is alive")
	}
	if rpctypes.ErrorDesc(err) == rpctypes.ErrorDesc(rpctypes.ErrGRPCPermissionDenied) || ctx2.Err() == nil {
		t.Fatalf("user2's waiting Campaign failed instead of waiting: %v", err)
	}
	t.Logf("user2's Campaign waited until its deadline: %v", err)
}
