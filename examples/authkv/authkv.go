// Package authkv is the authentication example of etcd's server and client (the end-to-end result
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
//     writer (x/<who>/...: once auth is on, only <who> writes or deletes it), and the writes
//     before the workload (the keys the deletes may remove, at revisions 2 to setupRev) are the
//     set-up's, as is a later repeat of one (a retried attempt of a set-up put: SetupWrite).
//
// Main calls only what the proofs specify or the client's auth side states as a contract
// (notes/decisions.md, "E2b of the auth plan"): etcdserver.NewServer, Start, v3rpc.Server (through
// common.Serve), net.Listen, (*grpc.Server).Serve on a goroutine, clientv3.New (with and without
// a user name), the client's Auth, KV and Watcher methods, metadata.AppendToOutgoingContext,
// context's WithTimeout and WithCancel. An error from a step of the set-up ends Main with Failed.
package authkv

import (
	"context"
	"sync"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/features"

	"github.com/mit-pdos/etcd-grove/examples/common"
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

// The range role r is granted, [lo, hi), and the users' passwords.
const (
	lo     = "a"
	hi     = "b"
	rootPw = "root-pw"
	uPw    = "u-pw"
	vPw    = "v-pw"
)

// The token the bad principal sends: never issued, since every token the simple provider issues
// is <prefix>.<index> (assign's Sprintf("%s.%d")) and this one has no dot (the provider's info
// refuses it before its map is read: isValidSimpleToken splits it in one part).
const badToken = "badtoken"

// How long a watch the server refuses is read before it is given up (its channel closes when its
// context ends, if the server's cancel did not close it first).
const refusedWatchTimeout = 2 * time.Second

// Principals is the principals: the users u and v, the client with no token (anon) and the one
// with a token no provider issued (bad).
func Principals() []string {
	return []string{"u", "v", "anon", "bad"}
}

// startServer starts the one member of a new cluster, as common.StartServer does, with the simple
// token provider (etcd's default, --auth-token simple) and etcd's default token TTL (300 seconds,
// --auth-token-ttl: embed's default; ServerConfig has none, and the simple provider's tokens with
// TTL 0 expire at its keeper's next tick).
func startServer(lg *zap.Logger) (*etcdserver.EtcdServer, error) {
	peer := types.URLs{{Scheme: "http", Host: peerAddr}}
	cfg := config.ServerConfig{
		Name:                   "authkv",
		DataDir:                "authkv.etcd",
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

// newUserClient connects a client that authenticates as user name with password pw (clientv3.New
// calls Authenticate when it dials, and the token is sent with every request).
func newUserClient(name string, pw string, lg *zap.Logger) (*clientv3.Client, error) {
	return clientv3.New(clientv3.Config{
		Endpoints:            []string{clientAddr},
		DialTimeout:          common.DialTimeout,
		DialKeepAliveTime:    common.KeepAliveTime,
		DialKeepAliveTimeout: common.KeepAliveTimeout,
		Username:             name,
		Password:             pw,
		Logger:               lg,
	})
}

// InRange reports whether key k is in [lo, hi), the range role r is granted.
func InRange(k string) bool {
	return lo <= k && k < hi
}

// Permitted reports whether the auth state lets principal who read or write key k: u, through
// role r, on [lo, hi); nobody else, anywhere.
func Permitted(who string, k string) bool {
	return who == "u" && InRange(k)
}

// keyOf is the key x/<who>/<n>: once auth is on, written and deleted only by who.
func keyOf(x string, who string, n string) string {
	return x + "/" + who + "/" + n
}

// reqCtx is a request's context, with the request timeout; the bad principal's carries its token.
func reqCtx(who string) (context.Context, context.CancelFunc) {
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	if who == "bad" {
		return metadata.AppendToOutgoingContext(ctx, "token", badToken), cancel
	}
	return ctx, cancel
}

// refused panics if err is nil: a request the auth state refuses who returned no error.
func refused(who string, what string, err error) {
	if err == nil {
		panic("authkv: " + who + "'s " + what + " was not refused")
	}
}

// checkKVs panics unless every key-value of a reply who received is one who may read.
func checkKVs(who string, kvs []*mvccpb.KeyValue) {
	for _, kv := range kvs {
		if !Permitted(who, string(kv.Key)) {
			panic("authkv: a reply to " + who + " holds a key " + who + " may not read")
		}
	}
}

// checkTxnReads panics unless every range response among the transaction reply's ops holds only
// keys who may read (one level: the workload's transactions that may succeed nest none).
func checkTxnReads(who string, ops []*etcdserverpb.ResponseOp) {
	for _, op := range ops {
		r := op.GetResponseRange()
		if r != nil {
			checkKVs(who, r.Kvs)
		}
	}
}

// Work runs principal who's workload through cli, checking each reply (above): its writes and
// reads inside [lo, hi) (permitted to u alone), reaching outside it, and its transactions, with
// each branch and a nested transaction reaching outside. A permitted request may fail (a
// timeout): only its reply, if any, is checked.
func Work(cli *clientv3.Client, who string) {
	in0 := keyOf("a", who, "0")
	out0 := keyOf("c", who, "0")

	// puts
	ctx, cancel := reqCtx(who)
	_, err := cli.Put(ctx, in0, "v0")
	cancel()
	if !Permitted(who, in0) {
		refused(who, "put in [a, b)", err)
	}
	ctx, cancel = reqCtx(who)
	_, err = cli.Put(ctx, out0, "v0")
	cancel()
	refused(who, "put outside [a, b)", err)

	// ranges: [lo, hi), a prefix outside it, a range reaching past hi
	ctx, cancel = reqCtx(who)
	g, err := cli.Get(ctx, lo, clientv3.WithRange(hi))
	cancel()
	if err == nil {
		if who != "u" {
			panic("authkv: " + who + "'s range of [a, b) was not refused")
		}
		checkKVs(who, g.Kvs)
	}
	ctx, cancel = reqCtx(who)
	_, err = cli.Get(ctx, "c/", clientv3.WithPrefix())
	cancel()
	refused(who, "range outside [a, b)", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Get(ctx, lo, clientv3.WithRange("d"))
	cancel()
	refused(who, "range past b", err)

	// transactions: one writing and reading [lo, hi) (permitted to u); one writing outside it in
	// its then branch, in its else branch, and in a nested transaction
	ctx, cancel = reqCtx(who)
	t, err := cli.Txn(ctx).Then(clientv3.OpPut(keyOf("a", who, "t"), "vt"),
		clientv3.OpGet(lo, clientv3.WithRange(hi))).Commit()
	cancel()
	if err == nil {
		if who != "u" {
			panic("authkv: " + who + "'s transaction in [a, b) was not refused")
		}
		checkTxnReads(who, t.Responses)
	}
	ctx, cancel = reqCtx(who)
	_, err = cli.Txn(ctx).Then(clientv3.OpPut(keyOf("a", who, "t1"), "vt"),
		clientv3.OpPut(keyOf("c", who, "t1"), "vt")).Commit()
	cancel()
	refused(who, "transaction writing outside [a, b)", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Txn(ctx).If(clientv3.Compare(clientv3.Value(in0), "=", "none")).
		Then(clientv3.OpPut(keyOf("a", who, "t2"), "vt")).
		Else(clientv3.OpPut(keyOf("c", who, "t2"), "vt")).Commit()
	cancel()
	refused(who, "transaction writing outside [a, b) in its else branch", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Txn(ctx).Then(clientv3.OpTxn(nil,
		[]clientv3.Op{clientv3.OpPut(keyOf("c", who, "t3"), "vt")}, nil)).Commit()
	cancel()
	refused(who, "nested transaction writing outside [a, b)", err)

	// deletes of the set-up's keys
	ctx, cancel = reqCtx(who)
	_, err = cli.Delete(ctx, keyOf("a", who, "d"))
	cancel()
	if !Permitted(who, keyOf("a", who, "d")) {
		refused(who, "delete in [a, b)", err)
	}
	ctx, cancel = reqCtx(who)
	_, err = cli.Delete(ctx, keyOf("c", who, "d"))
	cancel()
	refused(who, "delete outside [a, b)", err)

	// a watch of a prefix outside [lo, hi), from revision 1: refused, it reports nothing
	wctx, wcancel := context.WithTimeout(context.Background(), refusedWatchTimeout)
	if who == "bad" {
		wctx = metadata.AppendToOutgoingContext(wctx, "token", badToken)
	}
	wch := cli.Watcher.Watch(wctx, "c/", clientv3.WithPrefix(), clientv3.WithRev(1))
	for wresp := range wch {
		if len(wresp.Events) > 0 {
			panic("authkv: " + who + "'s watch outside [a, b) reported an event")
		}
	}
	wcancel()
}

// SetUp puts the keys the principals' deletes may remove (x/<who>/d, for x in a and c), then
// creates the auth state and enables auth, through cli (auth off: every request is allowed):
// user root with the root role, role r granted READWRITE on [lo, hi), user u with role r and user
// v with no role. It returns the last set-up write's revision, and false if a step failed.
func SetUp(cli *clientv3.Client) (int64, bool) {
	var rev int64
	for _, who := range Principals() {
		for _, x := range []string{"a", "c"} {
			ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
			p, err := cli.Put(ctx, keyOf(x, who, "d"), "setup")
			cancel()
			if err != nil {
				return 0, false
			}
			rev = p.Header.Revision
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	defer cancel()
	if _, err := cli.Auth.UserAdd(ctx, "root", rootPw); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.UserGrantRole(ctx, "root", "root"); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.RoleAdd(ctx, "r"); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.RoleGrantPermission(ctx, "r", lo, hi,
		clientv3.PermissionType(clientv3.PermReadWrite)); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.UserAdd(ctx, "u", uPw); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.UserGrantRole(ctx, "u", "r"); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.UserAdd(ctx, "v", vPw); err != nil {
		return 0, false
	}
	if _, err := cli.Auth.AuthEnable(ctx); err != nil {
		return 0, false
	}
	return rev, true
}

// Writer is the principal whose key k is once auth is on: the who of x/<who>/... for x in a and
// c, "" if k has no such shape.
func Writer(k string) string {
	for _, who := range Principals() {
		for _, x := range []string{"a", "c"} {
			p := x + "/" + who + "/"
			if len(k) > len(p) && k[:len(p)] == p {
				return who
			}
		}
	}
	return ""
}

// SetupWrite is whether e is one of SetUp's puts (keyOf(x, who, "d") for x in a and c, the value
// "setup"): an attempt of one may still be applied after SetUp returns (the client retries a
// refused put), so the history may hold it at any revision.
func SetupWrite(e common.Event) bool {
	for _, who := range Principals() {
		for _, x := range []string{"a", "c"} {
			if e.Put && e.Key == keyOf(x, who, "d") && e.Val == "setup" {
				return true
			}
		}
	}
	return false
}

// CheckHistory panics unless every watched event after the set-up (above revision setupRev) but
// root's last write (key endKey) and a repeat of a set-up put (SetupWrite) is a write its key's
// principal was permitted.
func CheckHistory(evs []common.Event, setupRev int64, endKey string) {
	for _, e := range evs {
		if e.Rev > setupRev && e.Key != endKey && !SetupWrite(e) && !Permitted(Writer(e.Key), e.Key) {
			panic("authkv: the history holds a write its principal was not permitted")
		}
	}
}

// LastIn is the revision of the last event of evs in [lo, hi) (0 if there is none).
func LastIn(evs []common.Event) int64 {
	var last int64
	for _, e := range evs {
		if InRange(e.Key) {
			last = e.Rev
		}
	}
	return last
}

// Main starts the member, sets up and enables auth, runs the four principals' workloads at once,
// then checks the history through root's watch, and u's watch of [lo, hi).
func Main() int {
	lg := zap.NewNop()
	s, err := startServer(lg)
	if err != nil {
		return Failed
	}
	if err := common.Serve(s, clientAddr); err != nil {
		return Failed
	}

	// The client with no user name: the set-up's, then the anon and bad principals'.
	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return Failed
	}
	setupRev, ok := SetUp(cli)
	if !ok {
		return Failed
	}
	root, err := newUserClient("root", rootPw, lg)
	if err != nil {
		return Failed
	}
	ucli, err := newUserClient("u", uPw, lg)
	if err != nil {
		return Failed
	}
	vcli, err := newUserClient("v", vPw, lg)
	if err != nil {
		return Failed
	}

	var wg sync.WaitGroup
	for _, who := range Principals() {
		c := cli
		if who == "u" {
			c = ucli
		} else if who == "v" {
			c = vcli
		}
		wg.Add(1)
		go func() {
			Work(c, who)
			wg.Done()
		}()
	}
	wg.Wait()

	// root's last write, after every principal's request has returned, and the history up to it.
	ctx, cancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	end, err := root.Put(ctx, "z/end", "end")
	cancel()
	if err != nil {
		return Failed
	}
	hctx, hcancel := context.WithCancel(context.Background())
	hch := root.Watcher.Watch(hctx, "", clientv3.WithPrefix(), clientv3.WithRev(1))
	evs, ok := common.Collect(hch, end.Header.Revision)
	hcancel()
	if !ok {
		return WatchEnded
	}
	CheckHistory(evs, setupRev, "z/end")

	// u's watch of [lo, hi) from revision 1, read up to the history's last event in it: it
	// reports only keys u may read.
	uctx, ucancel := context.WithCancel(context.Background())
	uch := ucli.Watcher.Watch(uctx, lo, clientv3.WithRange(hi), clientv3.WithRev(1))
	uevs, ok := common.Collect(uch, LastIn(evs))
	ucancel()
	if !ok {
		return WatchEnded
	}
	for _, e := range uevs {
		if !Permitted("u", e.Key) {
			panic("authkv: u's watch reported a key u may not read")
		}
	}
	return Ok
}
