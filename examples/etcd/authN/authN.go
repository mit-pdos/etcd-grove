// Package authN is auth3 (examples/etcd/auth3) for any number k of members (notes/authN-plan.md):
// the k members of a new cluster started in-process with auth on (etcdstart.StartMembersAuth: the
// simple token provider, etcd's default token TTL), each serving its raft handler on its own peer
// listener and its gRPC API on its client address. Through member 0, authkv's set-up (authwork.SetUp:
// the auth state set up and auth enabled); then a barrier at every member: root, through a client
// of the member, makes a linearizable read, so that each member has applied past the set-up
// (AuthEnable included) before any principal uses it (nonissues/etcd-watch-lagging-member-auth-off.md);
// then the four principals' workloads (authwork.Work), each through its own member, at once: the client
// with no token through member 0, u and the client with an invalid token through member 1 mod k, v
// through member 2 mod k (at k = 3, auth3's assignment); then, through member 0, the history check
// and, through u's member, u's watch check. Main panics if a member let a principal do what the auth
// state does not permit; the theorem to prove is that it does not.
//
// The members take the examples' no-snapshot settings (etcdstart.NoSnapCount, NoSnapCatchUp): a
// leader never sends a follower a snapshot.
package authN

import (
	"context"
	"sync"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/authwork"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' address ranges: member i's peer address is 127.0.0.1:(PeerBase+i) (its one peer
// URL http://<addr>, served by its raft handler), its client address 127.0.0.1:(ClientBase+i)
// (served by its gRPC API), ranges no other example uses, so that the examples' tests can run at
// once; for k <= 1000 the two ranges are disjoint and every port is at most 65535.
const (
	PeerBase   uint64 = 29000
	ClientBase uint64 = 30000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL,
// etcd computes each member's id: the first authN-<n> whose first 300 members' ids have distinct
// nonzero 16 low bits, also from the ids of examples/etcd/all's other clusters (etcd_safe's Hlow;
// TestMemberIDs here and there). Above 300 members the ids are not checked: etcd_authN_safe's
// premise on them may be false there.
const Token = "authN-133"

// newUserClient connects a client of addr that authenticates as user name with password pw
// (auth3's: clientv3.New calls Authenticate when it dials, and the token is sent with every
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
// returns), and reports whether it succeeded (auth3's).
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

// run is authkv's run (auth.Run) on the started members srvs of the members ms (len(srvs) =
// len(ms) >= 1): each member's gRPC API served at its client address; the set-up through member 0;
// the barrier at each member; the principals' workloads, anon through member 0, u and bad through
// member 1 mod k, v through member 2 mod k; root's history check through member 0 and u's watch
// check through u's member.
func run(srvs []*etcdserver.EtcdServer, ms []etcdstart.Member, lg *zap.Logger) int {
	k := uint64(len(ms))
	for j, m := range ms {
		if err := etcdstart.Serve(srvs[j], m.Client); err != nil {
			return auth.Failed
		}
	}

	a0 := ms[0].Client
	au := ms[1%k].Client
	av := ms[2%k].Client
	cli, err := etcdstart.NewClient(a0, lg)
	if err != nil {
		return auth.Failed
	}
	if !authwork.SetUp(cli) {
		return auth.Failed
	}
	for _, m := range ms {
		if !barrier(m.Client, lg) {
			return auth.Failed
		}
	}

	root, err := newUserClient(a0, "root", rootPw, lg)
	if err != nil {
		return auth.Failed
	}
	ucli, err := newUserClient(au, "u", uPw, lg)
	if err != nil {
		return auth.Failed
	}
	vcli, err := newUserClient(av, "v", vPw, lg)
	if err != nil {
		return auth.Failed
	}
	bcli, err := etcdstart.NewClient(au, lg)
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
			panic("authN: u's watch reported a key u may not read")
		}
	}
	return auth.Ok
}

// Main starts the k members of a new cluster with auth on (etcdstart.Members, StartMembersAuth),
// then runs authkv's set-up, workloads and checks across them (run), and returns its result
// (auth.Ok, auth.Failed, auth.WatchEnded); k = 0, or a member that fails to start, ends Main with
// auth.Failed.
func Main(k uint64) int {
	if k == 0 {
		return auth.Failed
	}
	lg := zap.NewNop()
	ms := etcdstart.Members("authN", k, PeerBase, ClientBase)
	srvs, err := etcdstart.StartMembersAuth(ms, Token, etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
	if err != nil {
		return auth.Failed
	}
	return run(srvs, ms, lg)
}
