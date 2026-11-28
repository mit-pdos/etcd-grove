// Package auth is the authentication example of etcd's server and client (the end-to-end result
// of notes/auth-plan.md, D-AU5): one etcd member started in-process with the simple token
// provider, its auth state set up and auth enabled through a client before any workload (a root
// user; a role r granted READWRITE on [a, b); a user u with the role and a user v without it),
// then four principals running the same workload of puts, ranges, deletes, transactions and
// watches inside and outside [a, b) at once: u and v (clients that authenticate with their
// passwords), a client with no token, and the same client sending a token no provider issued.
// Main panics if the server let a principal do what the auth state does not permit; the theorem
// to prove is that it does not (notes/decisions.md, "E2b of the auth plan").
//
// The checks, each a panic:
//   - every request the auth state refuses its principal returned an error (u's writes and reads
//     reaching outside [a, b), every request of v, of the client with no token and of the one
//     with the invalid token), and every watch of a range outside [a, b) reported no event;
//   - every reply a principal received (a range's, a transaction's reads', a watch's events)
//     holds only keys the principal may read (u: [a, b));
//   - the history: root's watch of every key from revision 1, read up to a last write root makes
//     after the workload, reports only writes their principal was permitted. A key names its
//     writer (x/<who>/...: once auth is on, only <who> writes or deletes it), but for the set-up's
//     puts (the keys the deletes may remove, with the value "setup": SetupWrite), which the check
//     admits wherever they are in the history.
//
// The workload and the checks are the library examples/lib/authwork's (moved there verbatim on
// 2026-11-27). Main calls only what the proofs specify or the client's auth side states as a contract
// (notes/decisions.md, "E2b of the auth plan"): etcdserver.NewServer, Start, v3rpc.Server (through
// etcdstart.Serve), net.Listen, (*grpc.Server).Serve on a goroutine, clientv3.New (with and without
// a user name), the client's Auth, KV and Watcher methods, metadata.AppendToOutgoingContext,
// context's WithTimeout and WithCancel. An error from a step of the set-up ends Main with Failed.
package auth

import (
	"context"
	"sync"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/lib/authwork"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23916"
	peerAddr   = "127.0.0.1:23926"
)

// Main's results: the checks passed, a step of the set-up failed, or a watch ended before it had
// reported the writes it was read for.
const (
	Ok         = 0
	Failed     = 1
	WatchEnded = 2
)

// The range role r is granted, [lo, hi), and the users' passwords: authwork's (the set-up's), which
// Run logs in with and watches.
const (
	lo     = "a"
	hi     = "b"
	rootPw = "root-pw"
	uPw    = "u-pw"
	vPw    = "v-pw"
)

// startServer starts the one member of a new cluster, as etcdstart.StartServer does, with the simple
// token provider (etcd's default, --auth-token simple) and etcd's default token TTL (300 seconds,
// --auth-token-ttl: embed's default; ServerConfig has none, and the simple provider's tokens with
// TTL 0 expire at its keeper's next tick).
func startServer(lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	cfg := config.ServerConfig{
		Name:                   "authkv",
		DataDir:                etcdstart.DataBase + "/" + "authkv.etcd",
		DedicatedWALDir:        etcdstart.WALBase + "/" + "authkv.etcd" + "/wal",
		InitialPeerURLsMap:     types.URLsMap{"authkv": peer},
		PeerURLs:               peer,
		ClientURLs:             types.URLs{{Scheme: "http", Host: clientAddr}},
		InitialClusterToken:    "authkv",
		NewCluster:             true,
		TickMs:                 100,
		ElectionTicks:          10,
		SnapshotCount:          etcdserver.DefaultSnapshotCount,
		SnapshotCatchUpEntries: 1 << 48,
		MaxTxnOps:              128,
		MaxRequestBytes:        1536 * 1024,
		AuthToken:              "simple",
		TokenTTL:               300,
		Logger:                 lg,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate("authkv", lg),
	}
	s, err := etcdserver.NewServer(cfg)
	if err != nil {
		return nil, err
	}
	s.Start()
	return s, nil
}

// newUserClient connects a client of addr that authenticates as user name with password pw
// (clientv3.New calls Authenticate when it dials, and the token is sent with every request).
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

// Main starts the member, then runs the set-up, the workloads and the checks through it (Run).
func Main() int {
	lg := zap.NewNop()
	s, err := startServer(lg)
	if err != nil {
		return Failed
	}
	return Run(s, clientAddr, lg)
}

// Run serves the started member s's gRPC API at addr, sets up and enables auth through a client
// of addr, runs the four principals' workloads at once through clients of addr, then checks the
// history through root's watch, and u's watch of [lo, hi). It is Main after the member's start,
// shared with examples/etcd/auth3, whose first member it runs on.
func Run(s *etcdserver.EtcdServer, addr string, lg *zap.Logger) int {
	if err := etcdstart.Serve(s, addr); err != nil {
		return Failed
	}

	// The client with no user name: the set-up's, then the anon and bad principals'.
	cli, err := etcdstart.NewClient(addr, lg)
	if err != nil {
		return Failed
	}
	if !authwork.SetUp(cli) {
		return Failed
	}
	root, err := newUserClient(addr, "root", rootPw, lg)
	if err != nil {
		return Failed
	}
	ucli, err := newUserClient(addr, "u", uPw, lg)
	if err != nil {
		return Failed
	}
	vcli, err := newUserClient(addr, "v", vPw, lg)
	if err != nil {
		return Failed
	}

	var wg sync.WaitGroup
	for _, who := range authwork.Principals() {
		c := cli
		if who == "u" {
			c = ucli
		} else if who == "v" {
			c = vcli
		}
		wg.Add(1)
		go func() {
			authwork.Work(c, who)
			wg.Done()
		}()
	}
	wg.Wait()

	// root's last write, after every principal's request has returned, and the history up to it.
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	end, err := root.Put(ctx, "z/end", "end")
	cancel()
	if err != nil {
		return Failed
	}
	hctx, hcancel := context.WithCancel(context.Background())
	hch := root.Watcher.Watch(hctx, "", clientv3.WithPrefix(), clientv3.WithRev(1))
	evs, ok := etcdstart.Collect(hch, end.Header.Revision)
	hcancel()
	if !ok {
		return WatchEnded
	}
	authwork.CheckHistory(evs, "z/end")

	// u's watch of [lo, hi) from revision 1, read up to the history's last event in it: it
	// reports only keys u may read.
	uctx, ucancel := context.WithCancel(context.Background())
	uch := ucli.Watcher.Watch(uctx, lo, clientv3.WithRange(hi), clientv3.WithRev(1))
	uevs, ok := etcdstart.Collect(uch, authwork.LastIn(evs))
	ucancel()
	if !ok {
		return WatchEnded
	}
	for _, e := range uevs {
		if !authwork.Permitted("u", e.Key) {
			panic("authkv: u's watch reported a key u may not read")
		}
	}
	return Ok
}
