// Package authwork is the authentication example's workload and checks, as a library (moved verbatim
// out of the single-process driver examples/etcd/auth, 2026-11-27, so that the multi-machine example,
// examples/etcd/dist, imports no driver): SetUp sets up and enables auth through a client (a root
// user; a role r granted READWRITE on [a, b); a user u with the role and a user v without it); Work is
// one principal's workload of puts, ranges, deletes, transactions and watches inside and outside
// [a, b), with its checks; CheckHistory checks root's watch of every key. Principals are u and v
// (clients that authenticate with their passwords), a client with no token (anon), and the same
// client sending a token no provider issued (bad).
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
package authwork

import (
	"context"
	"time"

	"google.golang.org/grpc/metadata"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
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
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
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
// v with no role. It returns false if a step failed.
func SetUp(cli *clientv3.Client) bool {
	for _, who := range Principals() {
		for _, x := range []string{"a", "c"} {
			ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
			_, err := cli.Put(ctx, keyOf(x, who, "d"), "setup")
			cancel()
			if err != nil {
				return false
			}
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	defer cancel()
	if _, err := cli.Auth.UserAdd(ctx, "root", rootPw); err != nil {
		return false
	}
	if _, err := cli.Auth.UserGrantRole(ctx, "root", "root"); err != nil {
		return false
	}
	if _, err := cli.Auth.RoleAdd(ctx, "r"); err != nil {
		return false
	}
	if _, err := cli.Auth.RoleGrantPermission(ctx, "r", lo, hi,
		clientv3.PermissionType(clientv3.PermReadWrite)); err != nil {
		return false
	}
	if _, err := cli.Auth.UserAdd(ctx, "u", uPw); err != nil {
		return false
	}
	if _, err := cli.Auth.UserGrantRole(ctx, "u", "r"); err != nil {
		return false
	}
	if _, err := cli.Auth.UserAdd(ctx, "v", vPw); err != nil {
		return false
	}
	if _, err := cli.Auth.AuthEnable(ctx); err != nil {
		return false
	}
	return true
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
// "setup"). CheckHistory admits one at any revision: in Go each is applied before SetUp returns
// (the client resends a Put only when the attempt was never sent), but the proof's model of the
// client lets an attempt be applied more than once (SetUp gives each put a persistent update),
// so the check does not depend on where in the history the set-up's puts are.
func SetupWrite(e etcdstart.Event) bool {
	for _, who := range Principals() {
		for _, x := range []string{"a", "c"} {
			if e.Put && e.Key == keyOf(x, who, "d") && e.Val == "setup" {
				return true
			}
		}
	}
	return false
}

// CheckHistory panics unless every watched event but root's last write (key endKey) and the
// set-up's puts (SetupWrite) is a write its key's principal was permitted.
func CheckHistory(evs []etcdstart.Event, endKey string) {
	for _, e := range evs {
		if e.Key != endKey && !SetupWrite(e) && !Permitted(Writer(e.Key), e.Key) {
			panic("authkv: the history holds a write its principal was not permitted")
		}
	}
}

// LastIn is the revision of the last event of evs in [lo, hi) (0 if there is none).
func LastIn(evs []etcdstart.Event) int64 {
	var last int64
	for _, e := range evs {
		if InRange(e.Key) {
			last = e.Rev
		}
	}
	return last
}
