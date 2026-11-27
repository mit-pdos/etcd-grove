package client

import (
	"context"

	"google.golang.org/grpc/metadata"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/authwork"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The authLease workload's constants (authlease's): the TTL of its leases (etcd's MaxLeaseTTL, so
// that none expires: Lean's Workload.needsNoExpiry), the token no provider issued, and its keys.
const (
	maxLeaseTTL = 9000000000
	badToken    = "badtoken"
	zKey        = "z/lease"
	aKey        = "a/lease"
	txnKey      = "a/txn"
	xKey        = "a/x"
)

// reqCtx (authlease's, copied) is a request's context with the request timeout; the bad
// principal's carries its token.
func reqCtx(who string) (context.Context, context.CancelFunc) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	if who == "bad" {
		return metadata.AppendToOutgoingContext(ctx, "token", badToken), cancel
	}
	return ctx, cancel
}

// refused (authlease's, copied) panics if err is nil: a request the auth state refuses who
// returned no error. Any error is a refusal.
func refused(who string, what string, err error) {
	if err == nil {
		panic("dist authLease: " + who + "'s " + what + " was not refused")
	}
}

// grantPut (authlease's, copied) grants a lease through cli and puts k with it; it reports the
// lease and whether both returned.
func grantPut(cli *clientv3.Client, k string) (clientv3.LeaseID, bool) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := cli.Lease.Grant(ctx, maxLeaseTTL)
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

// ownLease grants a lease of the client's own principal through cli, at the workload's TTL, and
// reports whether the grant returned. RunAuthLease's v makes one at its member before its foreign
// checks there, so that the member has served a lease request of the run. The lease holds no key
// and is neither Lz nor Lu: no check is about it, and foreign still asks v about Lu, u's lease,
// and its forbidden key a/lease.
func ownLease(cli *clientv3.Client) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err := cli.Lease.Grant(ctx, maxLeaseTTL)
	cancel()
	return err == nil
}

// noAuth (authlease's check 1, copied): who (no token, or the invalid one) is refused every lease
// method on id.
func noAuth(cli *clientv3.Client, who string, id clientv3.LeaseID) {
	ctx, cancel := reqCtx(who)
	_, err := cli.Lease.Grant(ctx, maxLeaseTTL)
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

// foreign (authlease's checks 3-5, adapted): who is refused the revocation of id, a lease of
// another principal (Lz or Lu, never who's own), and no reply discloses a key who cannot read: its
// TimeToLive with keys is refused or returns no key forbidden (the key of id who may not read), and
// its Leases returns lease IDs only (the result ignored: it carries no key).
//
// Refusal of TimeToLive with keys and of Leases is not demanded, as the single-process authlease's
// foreign does: there it tests etcd's all-or-nothing policy (checkLeaseTimeToLive and
// checkLeaseLeases refuse when the lease holds any key the user may not read), which etcd does not
// keep while a member applies a snapshot. applySnapshot calls lessor.Recover, which reloads every
// lease with no key attached, before kv.Restore re-attaches the keys (etcd's
// server/etcdserver/server.go applySnapshot, server/lease/lessor.go initAndRecover); both checks
// read the member's lessor and pass in between. A Go test at etcd's main fails on it:
// issues/etcd-lease-auth-snapshot-restore-keyless.md.
func foreign(cli *clientv3.Client, who string, id clientv3.LeaseID, forbidden string) {
	ctx, cancel := reqCtx(who)
	_, err := cli.Lease.Revoke(ctx, id)
	cancel()
	refused(who, "Revoke of a lease holding a key it may not write", err)
	ctx, cancel = reqCtx(who)
	resp, err := cli.Lease.TimeToLive(ctx, id, clientv3.WithAttachedKeys())
	cancel()
	if err == nil {
		for _, kb := range resp.Keys {
			if string(kb) == forbidden {
				panic("dist authLease: " + who + "'s TimeToLive with keys returned " + forbidden)
			}
		}
	}
	ctx, cancel = reqCtx(who)
	_, _ = cli.Lease.Leases(ctx)
	cancel()
}

// absent (authlease's, copied) reports whether root's Get of k succeeded and found no key; it
// panics if the Get succeeded and found one.
func absent(root *clientv3.Client, k string, why string) bool {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := root.Get(ctx, k)
	cancel()
	if err != nil {
		return false
	}
	if len(g.Kvs) != 0 {
		panic("dist authLease: " + k + " exists " + why)
	}
	return true
}

// RunAuthLease is the authLease workload (authlease's run minus its members' gRPC serving, copied;
// Lean: Workload.authLease; alone in its deployment, which has the token provider): authkv's
// set-up through eps[0] and barriers; root's lease Lz holding z/lease (eps[0]); u's lease Lu
// holding a/lease and, by a transaction, a/txn (eps[1 mod k]); v's own lease, holding no key
// (eps[2 mod k], ownLease); barriers; then authlease's checks
// 1-5, each principal through its own member (v: eps[2 mod k]), and u's revocation of Lu, after
// which root finds neither a/lease nor a/txn. A refusal is any error; every key the checks expect
// absent or attached is read by root after the refused request, so an error never stands for
// "not applied". With etcd's full peer handler (Q8) a follower's TimeToLive reaches the leader's
// lessor; the checks are refusals, made by the receiving member before it forwards.
func RunAuthLease(eps []string, ready func()) Result {
	k := len(eps)
	a0, au, av := eps[0], eps[1%k], eps[2%k]
	cli, err := newClient([]string{a0})
	if err != nil {
		return ended("authLease: a client failed to connect")
	}
	if !authwork.SetUp(cli) {
		return ended("authLease: the set-up failed")
	}
	if !barriers(eps) {
		return ended("authLease: a barrier failed")
	}
	root, err := newUserClient(a0, "root", rootPw)
	if err != nil {
		return ended("authLease: root's client failed to connect")
	}
	ucli, err := newUserClient(au, "u", uPw)
	if err != nil {
		return ended("authLease: u's client failed to connect")
	}
	vcli, err := newUserClient(av, "v", vPw)
	if err != nil {
		return ended("authLease: v's client failed to connect")
	}
	bcli, err := newClient([]string{au})
	if err != nil {
		return ended("authLease: bad's client failed to connect")
	}
	lz, ok := grantPut(root, zKey)
	if !ok {
		return ended("authLease: root's lease set-up failed")
	}
	lu, ok := grantPut(ucli, aKey)
	if !ok {
		return ended("authLease: u's lease set-up failed")
	}
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Txn(ctx).Then(clientv3.OpPut(txnKey, "v", clientv3.WithLease(lu))).Commit()
	cancel()
	if err != nil {
		return ended("authLease: u's leased transaction failed")
	}
	if !ownLease(vcli) {
		return ended("authLease: v's own lease grant failed")
	}
	if !barriers(eps) {
		return ended("authLease: a barrier failed")
	}
	ready()
	noAuth(cli, "anon", lu)
	noAuth(bcli, "bad", lu)
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Put(ctx, xKey, "v", clientv3.WithLease(lz))
	cancel()
	refused("u", "put with a lease holding a key it may not write", err)
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Txn(ctx).Then(clientv3.OpPut(xKey, "v", clientv3.WithLease(lz))).Commit()
	cancel()
	refused("u", "transaction putting with a lease holding a key it may not write", err)
	if !absent(root, xKey, "after u's refused puts") {
		return ended("authLease: root's read failed")
	}
	foreign(ucli, "u", lz, zKey)
	foreign(vcli, "v", lu, aKey)
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := root.Get(ctx, zKey)
	cancel()
	if err != nil {
		return ended("authLease: root's read failed")
	}
	if len(g.Kvs) != 1 || g.Kvs[0].Lease != int64(lz) {
		panic("dist authLease: z/lease is not attached to Lz after u's refused revocation")
	}
	ctx, cancel = context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	_, err = ucli.Lease.Revoke(ctx, lu)
	cancel()
	if err != nil {
		return ended("authLease: u's revocation failed")
	}
	if !absent(root, aKey, "after its lease's revocation") {
		return ended("authLease: root's read failed")
	}
	if !absent(root, txnKey, "after its lease's revocation") {
		return ended("authLease: root's read failed")
	}
	return checked()
}
