// Package auth3 is authkv (examples/etcd/auth) with a three-member cluster (notes/auth3-scope.md,
// variant A2): three etcd members started in-process with auth on (the simple token provider,
// etcd's default token TTL), each serving its raft handler on its own peer listener, as putget3's
// members do, and each serving its gRPC API. Through the first member, authkv's set-up (authwork.SetUp:
// the auth state set up and auth enabled); then a barrier: root, through a client of each member,
// makes a linearizable read, so that each member has applied past the set-up (AuthEnable included)
// before any principal uses it (a follower that has not would serve a watch with auth off:
// nonissues/etcd-watch-lagging-member-auth-off.md); then the four principals' workloads
// (authwork.Work), each through its own member (u through the second, v through the third, the client
// with no token through the first, the one with the invalid token through the second), at once;
// then, through the first member, the history check and, through the second, u's watch check.
// Main panics if a member let a principal do what the auth state does not permit; the theorem to
// prove is that it does not.
//
// The members take the examples' no-snapshot settings (etcdstart.NoSnapCount, NoSnapCatchUp): a
// leader never sends a follower a snapshot.
package auth3

import (
	"context"
	"net"
	"net/http"
	"sync"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/authwork"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' peer addresses (each member's one peer URL is http://<addr>, served by that
// member's raft handler) and client addresses (each served by its member's gRPC API: a plain
// host:port), not any other example's, so that the examples' tests can run at once.
const (
	peerAddr1   = "127.0.0.1:24131"
	peerAddr2   = "127.0.0.1:24132"
	peerAddr3   = "127.0.0.1:24133"
	clientAddr  = "127.0.0.1:24141"
	clientAddr2 = "127.0.0.1:24142"
	clientAddr3 = "127.0.0.1:24143"
)

// startMember starts member name of the new cluster whose initial members' peer URLs are cluster
// (token auth3), with auth's configuration (authkv's startServer: the simple token provider and
// etcd's default token TTL, 300 seconds), its peer URLs peer (the one URL http://peerAddr), its one
// client URL http://client and the examples' no-snapshot settings; it serves the member's raft
// handler on a listener at peerAddr (etcdstart.NewMember's), then starts the member.
func startMember(name string, peer types.URLs, peerAddr string, client string, cluster types.URLsMap,
	lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	cfg := config.ServerConfig{
		Name:                   name,
		DataDir:                etcdstart.DataBase + "/" + name + ".etcd",
		DedicatedWALDir:        etcdstart.WALBase + "/" + name + ".etcd" + "/wal",
		InitialPeerURLsMap:     cluster,
		PeerURLs:               peer,
		ClientURLs:             types.URLs{{Scheme: "http", Host: client}},
		InitialClusterToken:    "auth3",
		NewCluster:             true,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdstart.NoSnapCount,
		SnapshotCatchUpEntries: etcdstart.NoSnapCatchUp,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		AuthToken:              "simple",
		TokenTTL:               300,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate(name, lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return nil, err
	}
	// the member's peer URL is served by its own transport (D21b's deployment fact)
	l, err := net.Listen("tcp", peerAddr)
	if err != nil {
		return nil, err
	}
	go http.Serve(l, s.RaftHandler())
	s.Start()
	return s, nil
}

// newUserClient connects a client of addr that authenticates as user name with password pw
// (authkv's: clientv3.New calls Authenticate when it dials, and the token is sent with every
// request).
func newUserClient(addr string, name string, pw string, lg *zap.Logger) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints:            []string{addr},
		DialTimeout:          etcdstart.DialTimeout,
		DialKeepAliveTime:    etcdstart.KeepAliveTime,
		DialKeepAliveTimeout: etcdstart.KeepAliveTimeout,
		Username:             name,
		Password:             pw,
		Logger:               lg,
	})
}

// barrier makes root's linearizable read of the key z/barrier through a new client of addr (its
// read index is at least the set-up's AuthEnable, so the member has applied it when the read
// returns), and reports whether it succeeded.
func barrier(addr string, lg *zap.Logger) bool {
	root, err := newUserClient(addr, "root", rootPw, lg)
	if err != nil {
		return false
	}
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = root.Get(ctx, "z/barrier")
	cancel()
	return err == nil
}

// The users' passwords (authkv's SetUp's).
const (
	rootPw = "root-pw"
	uPw    = "u-pw"
	vPw    = "v-pw"
)

// run is authkv's run (auth.Run) on the three members s1, s2 and s3 at the client addresses a1, a2
// and a3: each member's gRPC API served; the set-up through s1; the barrier at each member; the
// principals' workloads, u through s2, v through s3, anon through s1, bad through s2; root's
// history check through s1 and u's watch check through s2.
func run(s1, s2, s3 *etcdserver.EtcdServer, a1, a2, a3 string, lg *zap.Logger) int {
	if err := etcdstart.Serve(s1, a1); err != nil {
		return auth.Failed
	}
	if err := etcdstart.Serve(s2, a2); err != nil {
		return auth.Failed
	}
	if err := etcdstart.Serve(s3, a3); err != nil {
		return auth.Failed
	}

	cli, err := etcdstart.NewClient(a1, lg)
	if err != nil {
		return auth.Failed
	}
	if !authwork.SetUp(cli) {
		return auth.Failed
	}
	if !barrier(a1, lg) {
		return auth.Failed
	}
	if !barrier(a2, lg) {
		return auth.Failed
	}
	if !barrier(a3, lg) {
		return auth.Failed
	}

	root, err := newUserClient(a1, "root", rootPw, lg)
	if err != nil {
		return auth.Failed
	}
	ucli, err := newUserClient(a2, "u", uPw, lg)
	if err != nil {
		return auth.Failed
	}
	vcli, err := newUserClient(a3, "v", vPw, lg)
	if err != nil {
		return auth.Failed
	}
	bcli, err := etcdstart.NewClient(a2, lg)
	if err != nil {
		return auth.Failed
	}

	var wg sync.WaitGroup
	for _, who := range authwork.Principals() {
		c := cli
		if who == "u" {
			c = ucli
		} else if who == "v" {
			c = vcli
		} else if who == "bad" {
			c = bcli
		}
		wg.Add(1)
		go func() {
			authwork.Work(c, who)
			wg.Done()
		}()
	}
	wg.Wait()

	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	end, err := root.Put(ctx, "z/end", "end")
	cancel()
	if err != nil {
		return auth.Failed
	}
	hctx, hcancel := context.WithCancel(context.Background())
	hch := root.Watcher.Watch(hctx, "", clientv3.WithPrefix(), clientv3.WithRev(1))
	evs, ok := etcdstart.Collect(hch, end.Header.Revision)
	hcancel()
	if !ok {
		return auth.WatchEnded
	}
	authwork.CheckHistory(evs, "z/end")

	uctx, ucancel := context.WithCancel(context.Background())
	uch := ucli.Watcher.Watch(uctx, "a", clientv3.WithRange("b"), clientv3.WithRev(1))
	uevs, ok := etcdstart.Collect(uch, authwork.LastIn(evs))
	ucancel()
	if !ok {
		return auth.WatchEnded
	}
	for _, e := range uevs {
		if !authwork.Permitted("u", e.Key) {
			panic("auth3: u's watch reported a key u may not read")
		}
	}
	return auth.Ok
}

// Main starts the three members of a new cluster with auth on, then runs authkv's set-up,
// workloads and checks across them (run), and returns its result (auth.Ok, auth.Failed,
// auth.WatchEnded); a member that fails to start ends Main with auth.Failed.
func Main() int {
	lg := zap.NewNop()
	peer1 := types.URLs{{Scheme: "http", Host: peerAddr1}}
	peer2 := types.URLs{{Scheme: "http", Host: peerAddr2}}
	peer3 := types.URLs{{Scheme: "http", Host: peerAddr3}}
	cluster := types.URLsMap{"auth3-1": peer1, "auth3-2": peer2, "auth3-3": peer3}

	s1, err := startMember("auth3-1", peer1, peerAddr1, clientAddr, cluster, lg)
	if err != nil {
		return auth.Failed
	}
	s2, err := startMember("auth3-2", peer2, peerAddr2, clientAddr2, cluster, lg)
	if err != nil {
		return auth.Failed
	}
	s3, err := startMember("auth3-3", peer3, peerAddr3, clientAddr3, cluster, lg)
	if err != nil {
		return auth.Failed
	}
	return run(s1, s2, s3, clientAddr, clientAddr2, clientAddr3, lg)
}
