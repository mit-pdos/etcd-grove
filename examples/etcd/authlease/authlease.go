// Package authlease is the lease rows of etcd's auth (notes/auth-lease-scope.md §1, §7) on authN's
// start for any number k of members (notes/auth-lease-s4-draft.md): the k members of a new
// cluster started in-process with auth on (etcdstart.StartMembersAuth: the simple token provider,
// etcd's default token TTL), each serving its raft handler on its own peer listener and its gRPC
// API on its client address. Through member 0, authkv's set-up (authwork.SetUp: a root user, a role r
// with READWRITE on [a, b), a user u with r, a user v without it, auth enabled); a barrier at every
// member (root's linearizable read: the member has applied the set-up); then the leases: root,
// through member 0, grants Lz and puts z/lease with it; u, through its member (1 mod k), grants Lu,
// puts a/lease with it and, in a transaction, a/txn with it; a second barrier at every member (each
// member's lessor holds those keys). Then the checks, each principal through its own member, each
// a panic if it fails:
//
//  1. the client with no token (member 0) and the client with a token no provider issued (member
//     1 mod k): Grant, Revoke(Lu), TimeToLive(Lu) with and without keys, and Leases are refused;
//  2. u: a put of a/x with Lz, and the same put inside a transaction, are refused (Lz holds z/lease,
//     which u may not write), and root's Get(a/x) then finds no key;
//  3. u: Revoke(Lz) is refused, and root's Get(z/lease) still finds z/lease, attached to Lz;
//  4. u: TimeToLive(Lz) with keys and Leases are refused (Lz holds z/lease, which u may not read);
//  5. v (member 2 mod k, no role): Revoke(Lu), TimeToLive(Lu) with keys and Leases are refused;
//
// and finally u revokes its own Lu (permitted: u may write a/lease and a/txn), and root's Get of
// a/lease and of a/txn, through member 0, find no key: the revocation deleted the keys attached.
//
// A refusal is any error. Nothing requires a permitted call to succeed: an error from a step of the
// set-up, of the lease set-up, of a barrier, of root's reads or of u's last revocation ends Main
// with Failed. No lease expires during the run: the TTL is etcd's MaxLeaseTTL (about 285 years), so
// that the process-wide premise that no lease expires (lease.leasesNoExpiry) holds however long the
// process runs, also when examples/etcd/all runs this example beside unbounded workloads.
//
// With the examples' peers (the raft handler only), a permitted TimeToLive or KeepAlive at a member
// other than the leader reports the lease absent (TTL -1, no keys): the follower's forwarding to
// the leader's /leases path gets a 404 (notes/auth-lease-scope.md §7.1, E10). The checks are
// refusals, made by the receiving member before it forwards, so they are unaffected.
//
// The members take the examples' no-snapshot settings (etcdstart.NoSnapCount, NoSnapCatchUp).
package authlease

import (
	"context"

	"go.uber.org/zap"
	"google.golang.org/grpc/metadata"

	clientv3 "go.etcd.io/etcd/client/v3"

	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/lib/authwork"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' address ranges: member i's peer address is 127.0.0.1:(PeerBase+i), its client
// address 127.0.0.1:(ClientBase+i), ranges no other example uses, below Linux's ephemeral range
// (32768-60999), so that the examples' tests can run at once; for k <= 1000 the two ranges are
// disjoint.
const (
	PeerBase   uint64 = 16000
	ClientBase uint64 = 17000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL,
// etcd computes each member's id: the first authlease-<n> whose first 300 members' ids have
// distinct 15 low bits and nonzero 16 low bits, the 16 low bits also distinct from the ids of
// examples/etcd/all's other clusters (etcd_safe's Hlow; TestMemberIDs here and there). Above 300
// members the ids are not checked: etcd_authlease_safe's premises on them may be false there. LeaseGrant gives a grant with no
// ID its member's next request id with bit 63 cleared, which keeps 15 bits of the member id
// (issues/etcd-lease-id-mask-member-prefix.md): with these ids no two members' lease ids collide.
const Token = "authlease-1787"

// The TTL the leases are granted with, in seconds: etcd's lease.MaxLeaseTTL, the largest Grant
// accepts (lessor.go refuses only a TTL above it), so that no lease of the run ever expires, however
// long the process runs (examples/etcd/all's etcd_safe composes this example with workloads of any
// length, under the one process-wide premise lease.leasesNoExpiry).
const grantTTL = 9000000000

// The users' passwords (authkv's SetUp's), and the token no provider issued (authkv's).
const (
	rootPw   = "root-pw"
	uPw      = "u-pw"
	vPw      = "v-pw"
	badToken = "badtoken"
)

// The keys: z/lease (outside [a, b): root's), a/lease and a/txn (inside: u's), a/x (inside: the
// key of u's refused leased puts).
const (
	zKey   = "z/lease"
	aKey   = "a/lease"
	txnKey = "a/txn"
	xKey   = "a/x"
)

// newUserClient connects a client of addr that authenticates as user name with password pw
// (auth3's).
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

// reqCtx is a request's context, with the request timeout; the bad principal's carries its token
// (authkv's).
func reqCtx(who string) (context.Context, context.CancelFunc) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	if who == "bad" {
		return metadata.AppendToOutgoingContext(ctx, "token", badToken), cancel
	}
	return ctx, cancel
}

// refused panics if err is nil: a request the auth state refuses who returned no error.
func refused(who string, what string, err error) {
	if err == nil {
		panic("authlease: " + who + "'s " + what + " was not refused")
	}
}

// barrier makes root's linearizable read of the key z/barrier through a new client of addr, and
// reports whether it succeeded (auth3's): the member has then applied every entry committed
// before the read.
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

// barriers runs barrier at every member, and reports whether every one succeeded.
func barriers(ms []etcdstart.Member, lg *zap.Logger) bool {
	for _, m := range ms {
		if !barrier(m.Client, lg) {
			return false
		}
	}
	return true
}

// grantPut grants a lease through cli and puts k with it; it reports the lease and whether both
// succeeded.
func grantPut(cli *clientv3.Client, k string) (clientv3.LeaseID, bool) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := cli.Lease.Grant(ctx, grantTTL)
	cancel()
	if err != nil {
		return 0, false
	}
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = cli.Put(ctx, k, "v", clientv3.WithLease(g.ID))
	cancel()
	if err != nil {
		return 0, false
	}
	return g.ID, true
}

// noAuth is check 1: who (the client with no token, or the one with the invalid token) is refused
// every lease method on id.
func noAuth(cli *clientv3.Client, who string, id clientv3.LeaseID) {
	ctx, cancel := reqCtx(who)
	_, err := cli.Lease.Grant(ctx, grantTTL)
	cancel()
	refused(who, "Grant", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Lease.Revoke(ctx, id)
	cancel()
	refused(who, "Revoke", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Lease.TimeToLive(ctx, id)
	cancel()
	refused(who, "TimeToLive", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Lease.TimeToLive(ctx, id, clientv3.WithAttachedKeys())
	cancel()
	refused(who, "TimeToLive with keys", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Lease.Leases(ctx)
	cancel()
	refused(who, "Leases", err)
}

// foreign is checks 4 and 5 (and 3's refusal): who is refused the revocation of id, its
// TimeToLive with keys and the listing of the leases, id holding a key who may not touch.
func foreign(cli *clientv3.Client, who string, id clientv3.LeaseID) {
	ctx, cancel := reqCtx(who)
	_, err := cli.Lease.Revoke(ctx, id)
	cancel()
	refused(who, "Revoke of a lease holding a key it may not write", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Lease.TimeToLive(ctx, id, clientv3.WithAttachedKeys())
	cancel()
	refused(who, "TimeToLive with keys of a lease holding a key it may not read", err)
	ctx, cancel = reqCtx(who)
	_, err = cli.Lease.Leases(ctx)
	cancel()
	refused(who, "Leases, a lease holding a key it may not read", err)
}

// absent reports whether root's Get of k through cli succeeded and found no key; it panics if
// the Get succeeded and found one (what the caller expects to be absent).
func absent(root *clientv3.Client, k string, why string) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := root.Get(ctx, k)
	cancel()
	if err != nil {
		return false
	}
	if len(g.Kvs) != 0 {
		panic("authlease: " + k + " exists " + why)
	}
	return true
}

// run is the set-up, the lease set-up and the checks (see the package comment) on the started
// members srvs of the members ms (len(srvs) = len(ms) >= 1).
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
	if !barriers(ms, lg) {
		return auth.Failed
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

	// the leases: root's Lz holding z/lease; u's Lu holding a/lease and, by a transaction, a/txn
	lz, ok := grantPut(root, zKey)
	if !ok {
		return auth.Failed
	}
	lu, ok := grantPut(ucli, aKey)
	if !ok {
		return auth.Failed
	}
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Txn(ctx).Then(clientv3.OpPut(txnKey, "v", clientv3.WithLease(lu))).Commit()
	cancel()
	if err != nil {
		return auth.Failed
	}
	if !barriers(ms, lg) {
		return auth.Failed
	}

	// 1. no token, an invalid token
	noAuth(cli, "anon", lu)
	noAuth(bcli, "bad", lu)

	// 2. u's leased puts with root's lease, at top level and in a transaction
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Put(ctx, xKey, "v", clientv3.WithLease(lz))
	cancel()
	refused("u", "put with a lease holding a key it may not write", err)
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Txn(ctx).Then(clientv3.OpPut(xKey, "v", clientv3.WithLease(lz))).Commit()
	cancel()
	refused("u", "transaction putting with a lease holding a key it may not write", err)
	if !absent(root, xKey, "after u's refused puts") {
		return auth.Failed
	}

	// 3, 4. u against Lz; 5. v against Lu
	foreign(ucli, "u", lz)
	foreign(vcli, "v", lu)
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := root.Get(ctx, zKey)
	cancel()
	if err != nil {
		return auth.Failed
	}
	if len(g.Kvs) != 1 || g.Kvs[0].Lease != int64(lz) {
		panic("authlease: z/lease is not attached to Lz after u's refused revocation")
	}

	// u revokes its own lease: its keys are deleted
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Lease.Revoke(ctx, lu)
	cancel()
	if err != nil {
		return auth.Failed
	}
	if !absent(root, aKey, "after its lease's revocation") {
		return auth.Failed
	}
	if !absent(root, txnKey, "after its lease's revocation") {
		return auth.Failed
	}
	return auth.Ok
}

// Main starts the k members of a new cluster with auth on (etcdstart.Members, StartMembersAuth),
// then runs the lease set-up and checks across them (run), and returns its result (auth.Ok,
// auth.Failed); k = 0, or a member that fails to start, ends Main with auth.Failed.
func Main(k uint64) int {
	if k == 0 {
		return auth.Failed
	}
	lg := zap.NewNop()
	ms := etcdstart.Members("authlease", k, PeerBase, ClientBase)
	srvs, err := etcdstart.StartMembersAuth(ms, Token, etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
	if err != nil {
		return auth.Failed
	}
	return run(srvs, ms, lg)
}
