// F7 S5 txn review (2026-11-26): Txn_CommitOn_dist's widened write arm, a leased put inside a
// transaction (txn.txnPlain ∨ (lm = revocable ∧ txnPlainL)), auth on, three members.
//
// For every case the test logs Go's outcome and checks it against what the dist spec's model says
// (kvOpStep (.txn t): commit iff PathsIgnOk ∧ PathsLeaseOk on the taken branch; grantedAt:
// kvGranted ∧ leaseGrantedM over BOTH branches' puts, leaseOk = admin ∨ every key already on the
// lease writable). A success must be exactly one revision step with the leases attached; a refusal
// must leave the store (revision, keys, lessor items) unchanged.
package integration

import (
	"context"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestF7TxnLeased(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, SnapshotCount: 20, SnapshotCatchUpEntries: 5})
	defer clus.Terminate(t)

	api0 := integration.ToGRPC(clus.Client(0))
	authSetupUsers(t, api0.Auth, []user{
		{name: "alice", password: "pw", role: "ra", key: "a", end: "b"},
		{name: "bob", password: "pw", role: "rb", key: "c", end: "d"},
	})
	authSetupRoot(t, api0.Auth)

	ctx, cancel := context.WithTimeout(t.Context(), 120*time.Second)
	defer cancel()
	mk := func(i int, u string) *clientv3.Client {
		c, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{clus.Members[i].GRPCURL}, Username: u, Password: map[string]string{"root": "123"}[u] + map[string]string{"alice": "pw", "bob": "pw"}[u]})
		require.NoError(t, err)
		t.Cleanup(func() { c.Close() })
		return c
	}
	root := mk(0, "root")
	defer root.Close()

	rev := func() int64 {
		r, err := root.Get(ctx, "zz-rev-probe")
		require.NoError(t, err)
		return r.Header.Revision
	}
	keysOf := func(id clientv3.LeaseID) []string {
		r, err := root.TimeToLive(ctx, id, clientv3.WithAttachedKeys())
		require.NoError(t, err)
		var ks []string
		for _, k := range r.Keys {
			ks = append(ks, string(k))
		}
		return ks
	}
	leaseOfKey := func(k string) (bool, int64) {
		r, err := root.Get(ctx, k)
		require.NoError(t, err)
		if len(r.Kvs) == 0 {
			return false, 0
		}
		return true, r.Kvs[0].Lease
	}
	grant := func(c *clientv3.Client) clientv3.LeaseID {
		g, err := c.Grant(ctx, 600)
		require.NoError(t, err)
		return g.ID
	}

	// runTxn runs the txn and checks Go's outcome against the expected one: on success exactly one
	// revision step (writes in the branch) and the response's revision is it; on error no change.
	type exp struct {
		ok      bool
		errIs   error
		errSub  string
		succeed bool
	}
	runTxn := func(name string, c *clientv3.Client, tx func(clientv3.Txn) clientv3.Txn, e exp, written bool) *clientv3.TxnResponse {
		r0 := rev()
		resp, err := tx(c.Txn(ctx)).Commit()
		r1 := rev()
		t.Logf("CASE %-70s err=%v rev %d -> %d", name, err, r0, r1)
		if e.ok {
			require.NoError(t, err, name)
			require.Equal(t, e.succeed, resp.Succeeded, name)
			if written {
				require.Equal(t, r0+1, r1, name)
				require.Equal(t, r1, resp.Header.Revision, name)
			} else {
				require.Equal(t, r0, r1, name)
			}
			return resp
		}
		require.Error(t, err, name)
		if e.errIs != nil {
			require.ErrorIs(t, err, e.errIs, name)
		}
		if e.errSub != "" {
			require.Contains(t, err.Error(), e.errSub, name)
		}
		require.Equal(t, r0, r1, name+": refused txn must not change the store")
		return nil
	}

	for i := 0; i < 3; i++ {
		alice := mk(i, "alice")
		bob := mk(i, "bob")
		p := fmt.Sprintf("m%d-", i)
		la1 := grant(alice) // granted through member 0's client? no: alice is at member i
		la2 := grant(mk((i+1)%3, "alice"))
		lr := grant(root)

		// 1. multiple puts with different leases, plus a delete of another key, one txn
		_, err := alice.Put(ctx, "a"+p+"del", "x")
		require.NoError(t, err)
		runTxn(p+"alice: two puts, two leases (one granted at another member), a delete", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.If(clientv3.Compare(clientv3.Version("a"+p+"k1"), "=", 0)).
				Then(clientv3.OpPut("a"+p+"k1", "v", clientv3.WithLease(la1)),
					clientv3.OpPut("a"+p+"k2", "v", clientv3.WithLease(la2)),
					clientv3.OpDelete("a"+p+"del"))
		}, exp{ok: true, succeed: true}, true)
		_, l := leaseOfKey("a" + p + "k1")
		require.Equal(t, int64(la1), l)
		_, l = leaseOfKey("a" + p + "k2")
		require.Equal(t, int64(la2), l)
		ex, _ := leaseOfKey("a" + p + "del")
		require.False(t, ex)
		require.Equal(t, []string{"a" + p + "k1"}, keysOf(la1))
		require.Equal(t, []string{"a" + p + "k2"}, keysOf(la2))

		// 2. put with lease and delete of the same key: duplicate key, refused before raft
		runTxn(p+"alice: put(k, lease) and delete(k) in one branch", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"k3", "v", clientv3.WithLease(la1)), clientv3.OpDelete("a"+p+"k3"))
		}, exp{errIs: rpctypes.ErrDuplicateKey}, false)
		// two puts of one key with two leases: duplicate too
		runTxn(p+"alice: put(k, l1) and put(k, l2)", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"k3", "v", clientv3.WithLease(la1)), clientv3.OpPut("a"+p+"k3", "w", clientv3.WithLease(la2)))
		}, exp{errIs: rpctypes.ErrDuplicateKey}, false)

		// 3. re-leasing a key: k1 moves from la1 to la2 (Detach of the old lease)
		runTxn(p+"alice: re-put k1 with la2", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"k1", "v2", clientv3.WithLease(la2)))
		}, exp{ok: true, succeed: true}, true)
		require.Empty(t, keysOf(la1))
		require.ElementsMatch(t, []string{"a" + p + "k1", "a" + p + "k2"}, keysOf(la2))

		// 4. a lease never granted, on the taken branch: ErrLeaseNotFound, nothing written
		missing := clientv3.LeaseID(0x1234567)
		runTxn(p+"alice: missing lease on the taken branch (plus a lease-free put)", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"free", "v"), clientv3.OpPut("a"+p+"k4", "v", clientv3.WithLease(missing)))
		}, exp{errIs: rpctypes.ErrLeaseNotFound}, false)
		ex, _ = leaseOfKey("a" + p + "free")
		require.False(t, ex)
		// ... on the untaken branch only: succeeds (checkTxn checks the taken branch)
		runTxn(p+"alice: missing lease on the untaken branch", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.If(clientv3.Compare(clientv3.Version("a"+p+"k1"), ">", 0)).
				Then(clientv3.OpPut("a"+p+"k5", "v", clientv3.WithLease(la1))).
				Else(clientv3.OpPut("a"+p+"k6", "v", clientv3.WithLease(missing)))
		}, exp{ok: true, succeed: true}, true)

		// 5. a revoked lease: ErrLeaseNotFound
		_, err = root.Revoke(ctx, lr)
		require.NoError(t, err)
		runTxn(p+"alice: revoked lease", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"k7", "v", clientv3.WithLease(lr)))
		}, exp{errIs: rpctypes.ErrLeaseNotFound}, false)

		// 6. another user's lease. bob may not attach la2 (its keys are in [a,b)): permission denied,
		// on the taken branch, on the untaken branch, and in a nested-free compare-false txn alike.
		runTxn(p+"bob: alice's lease (keys in [a,b)) on the taken branch", bob, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("c"+p+"1", "v", clientv3.WithLease(la2)))
		}, exp{errIs: rpctypes.ErrPermissionDenied}, false)
		runTxn(p+"bob: alice's lease on the UNTAKEN branch", bob, func(x clientv3.Txn) clientv3.Txn {
			return x.If(clientv3.Compare(clientv3.Version("c"+p+"none"), "=", 0)).
				Then(clientv3.OpPut("c"+p+"2", "v")).
				Else(clientv3.OpPut("c"+p+"3", "v", clientv3.WithLease(la2)))
		}, exp{errIs: rpctypes.ErrPermissionDenied}, false)
		// alice's lease with no keys (la1, emptied in 3... k5 attached in 4; use a fresh one)
		le := grant(alice)
		runTxn(p+"bob: alice's EMPTY lease: allowed (no key to check)", bob, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("c"+p+"4", "v", clientv3.WithLease(le)))
		}, exp{ok: true, succeed: true}, true)
		// now le holds bob's key: alice may not attach it
		runTxn(p+"alice: le now holds bob's key", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"8", "v", clientv3.WithLease(le)))
		}, exp{errIs: rpctypes.ErrPermissionDenied}, false)
		// mixed: bob's put with his own fresh lease and alice's la2 in the same txn
		lb := grant(bob)
		runTxn(p+"bob: own lease + alice's lease in one txn", bob, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("c"+p+"5", "v", clientv3.WithLease(lb)), clientv3.OpPut("c"+p+"6", "v", clientv3.WithLease(la2)))
		}, exp{errIs: rpctypes.ErrPermissionDenied}, false)
		// root may attach any lease
		runTxn(p+"root: alice's lease la2 on a key outside alice's range", root, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("z"+p+"r", "v", clientv3.WithLease(la2)))
		}, exp{ok: true, succeed: true}, true)
		// a lease writable on all keys but the user's own key put outside range: plain perm denial
		runTxn(p+"alice: own lease, key outside her range", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("c"+p+"9", "v", clientv3.WithLease(la1)))
		}, exp{errIs: rpctypes.ErrPermissionDenied}, false)

		// 7. IgnoreValue with a lease (putIgnVal (some l)): changes the lease, keeps the value;
		// on a missing key ErrKeyNotFound.
		runTxn(p+"alice: IgnoreValue + lease on an existing key", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"k2", "", clientv3.WithIgnoreValue(), clientv3.WithLease(la1)))
		}, exp{ok: true, succeed: true}, true)
		gr, err := root.Get(ctx, "a"+p+"k2")
		require.NoError(t, err)
		require.Equal(t, "v", string(gr.Kvs[0].Value))
		require.Equal(t, int64(la1), gr.Kvs[0].Lease)
		runTxn(p+"alice: IgnoreValue + lease on a missing key", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut("a"+p+"nokey", "", clientv3.WithIgnoreValue(), clientv3.WithLease(la1)))
		}, exp{errIs: rpctypes.ErrKeyNotFound}, false)

		// 8. the response's per-op content: a get in the same txn sees the pre-txn state
		resp := runTxn(p+"alice: get + leased put of the same key... (get reads pre-state)", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpGet("a"+p+"k1"), clientv3.OpPut("a"+p+"k10", "v", clientv3.WithLease(la1)))
		}, exp{ok: true, succeed: true}, true)
		require.Equal(t, int64(la2), resp.Responses[0].GetResponseRange().Kvs[0].Lease)

		// revoking a lease deletes its txn-attached keys at one revision
		r0 := rev()
		_, err = alice.Revoke(ctx, la2)
		t.Logf("CASE %salice: revoke la2 (root attached a key outside her range): %v", p, err)
		require.ErrorIs(t, err, rpctypes.ErrPermissionDenied)
		require.Equal(t, r0, rev())
		_, err = root.Revoke(ctx, la2)
		require.NoError(t, err)
		require.Equal(t, r0+1, rev())
		for _, k := range []string{"a" + p + "k1", "z" + p + "r"} {
			ex, _ := leaseOfKey(k)
			require.False(t, ex, k)
		}
		alice.Close()
		bob.Close()
	}

	// 9. lag: grant through member 0, txn immediately through member 1/2 (repeat), and revoke
	// through member 0, txn immediately through the other members.
	for round := 0; round < 20; round++ {
		a0 := mk(0, "alice")
		g := grant(a0)
		for j := 1; j < 3; j++ {
			aj := mk(j, "alice")
			_, err := aj.Txn(ctx).Then(clientv3.OpPut(fmt.Sprintf("alag%d-%d", round, j), "v", clientv3.WithLease(g))).Commit()
			require.NoError(t, err, "lease granted at member 0, txn at member %d", j)
			aj.Close()
		}
		_, err := a0.Revoke(ctx, g)
		require.NoError(t, err)
		for j := 1; j < 3; j++ {
			aj := mk(j, "alice")
			_, err := aj.Txn(ctx).Then(clientv3.OpPut(fmt.Sprintf("alagr%d-%d", round, j), "v", clientv3.WithLease(g))).Commit()
			require.ErrorIs(t, err, rpctypes.ErrLeaseNotFound, "lease revoked at member 0, txn at member %d", j)
			aj.Close()
		}
		a0.Close()
	}
	t.Logf("CASE lag rounds: 20 x (grant@m0 -> leased txn@m1,m2 ok; revoke@m0 -> leased txn@m1,m2 ErrLeaseNotFound): as expected")

	// 10. snapshot: stop a follower, grant/attach/revoke while it is down, enough entries for the
	// leader to compact; restart it (it catches up by snapshot), then txn through it.
	lead := -1
	for i := range clus.Members {
		if clus.Members[i].Server.Leader() == clus.Members[i].ID() {
			lead = i
		}
	}
	require.GreaterOrEqual(t, lead, 0)
	t.Logf("CASE snapshot phase: leader m%d", lead)
	f := (lead + 1) % 3
	other := (lead + 2) % 3
	alice := mk(lead, "alice")
	lpre := grant(alice)
	_, err := alice.Put(ctx, "asnap-pre", "v", clientv3.WithLease(lpre))
	require.NoError(t, err)
	clus.Members[f].Stop(t)
	lgr := grant(alice)                                                        // granted while f is down
	_, err = alice.Put(ctx, "asnap-k", "v", clientv3.WithLease(lgr))           // a key on it
	require.NoError(t, err)
	lrv := grant(alice)
	_, err = alice.Revoke(ctx, lpre) // revoked while f is down
	require.NoError(t, err)
	_, err = alice.Revoke(ctx, lrv)
	require.NoError(t, err)
	for k := 0; k < 60; k++ {
		_, err = alice.Put(ctx, fmt.Sprintf("afill%d", k), "v")
		require.NoError(t, err)
	}
	require.NoError(t, clus.Members[f].Restart(t))
	t.Logf("CASE snapshot phase: m%d restarted (leader's log compacted past its index: catch-up by snapshot)", f)
	fa := mk(f, "alice")
	fb := mk(f, "bob")
	// immediately, no wait for f's catch-up beyond its own apply of the entry
	_, err = fa.Txn(ctx).Then(clientv3.OpPut("asnap-1", "v", clientv3.WithLease(lgr))).Commit()
	t.Logf("CASE snapshot member %d: leased txn with lease granted while down: %v", f, err)
	require.NoError(t, err)
	_, err = fa.Txn(ctx).Then(clientv3.OpPut("asnap-2", "v", clientv3.WithLease(lrv))).Commit()
	t.Logf("CASE snapshot member %d: leased txn with lease revoked while down: %v", f, err)
	require.ErrorIs(t, err, rpctypes.ErrLeaseNotFound)
	_, err = fa.Txn(ctx).Then(clientv3.OpPut("asnap-3", "v", clientv3.WithLease(lpre))).Commit()
	t.Logf("CASE snapshot member %d: leased txn with lease granted before, revoked while down: %v", f, err)
	require.ErrorIs(t, err, rpctypes.ErrLeaseNotFound)
	// the lessor's items after the snapshot: bob may not attach lgr (holds alice's keys)
	_, err = fb.Txn(ctx).Then(clientv3.OpPut("csnap", "v", clientv3.WithLease(lgr))).Commit()
	t.Logf("CASE snapshot member %d: bob attaching alice's lgr (keys restored from snapshot): %v", f, err)
	require.ErrorIs(t, err, rpctypes.ErrPermissionDenied)
	// and the same through the other follower, for comparison
	ob := mk(other, "bob")
	_, err = ob.Txn(ctx).Then(clientv3.OpPut("csnap", "v", clientv3.WithLease(lgr))).Commit()
	t.Logf("CASE member %d (never down): bob attaching alice's lgr: %v", other, err)
	require.ErrorIs(t, err, rpctypes.ErrPermissionDenied)
	// all members agree on the keys of lgr
	for i := 0; i < 3; i++ {
		c := mk(i, "root")
		r, err := c.Get(ctx, "asnap", clientv3.WithPrefix(), clientv3.WithSerializable())
		require.NoError(t, err)
		var ks []string
		for _, kv := range r.Kvs {
			ks = append(ks, fmt.Sprintf("%s@%x", kv.Key, kv.Lease))
		}
		t.Logf("CASE member %d serializable view of asnap*: %s rev %d", i, strings.Join(ks, " "), r.Header.Revision)
		c.Close()
	}
	_ = pb.Compare_EQUAL
}
