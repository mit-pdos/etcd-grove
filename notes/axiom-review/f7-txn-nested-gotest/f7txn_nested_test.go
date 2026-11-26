// F7 S11 txn review (2026-11-26): Txn_CommitOn_dist widened to nested transactions (no
// TxnModel.plain; the write arm adds txnNestOk), auth on, three members.
//
// Each case logs Go's outcome and checks it against the dist spec's model: grantedAt = kvGranted
// over reqPerms (the comparisons' reads and BOTH branches' operations, recursively, `opPerms`);
// kvOpStep (.txn t) = commit of srvRunTxn (nested verdicts at the read state s0, operations in
// order); a success is exactly one revision step when the taken path writes (none otherwise), its
// response's nested verdicts and results srvRunTxn's; a refusal leaves the store unchanged.
package integration

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestF7TxnNested(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3})
	defer clus.Terminate(t)

	api0 := integration.ToGRPC(clus.Client(0))
	authSetupUsers(t, api0.Auth, []user{
		{name: "alice", password: "pw", role: "ra", key: "a", end: "b"},
		{name: "wo", password: "pw", role: "rw", perm: "write", key: "a", end: "b"},
	})
	authSetupRoot(t, api0.Auth)

	ctx, cancel := context.WithTimeout(t.Context(), 120*time.Second)
	defer cancel()
	pw := map[string]string{"root": "123", "alice": "pw", "wo": "pw"}
	mk := func(i int, u string) *clientv3.Client {
		c, err := integration.NewClient(t, clientv3.Config{Endpoints: []string{clus.Members[i].GRPCURL}, Username: u, Password: pw[u]})
		require.NoError(t, err)
		t.Cleanup(func() { c.Close() })
		return c
	}
	root := mk(0, "root")

	rev := func() int64 {
		r, err := root.Get(ctx, "zz-rev-probe")
		require.NoError(t, err)
		return r.Header.Revision
	}
	val := func(k string) string {
		r, err := root.Get(ctx, k)
		require.NoError(t, err)
		if len(r.Kvs) == 0 {
			return "<none>"
		}
		return string(r.Kvs[0].Value)
	}
	nest := func(depth int, inner clientv3.Op) clientv3.Op {
		op := inner
		for d := 0; d < depth; d++ {
			op = clientv3.OpTxn(nil, []clientv3.Op{op}, nil)
		}
		return op
	}

	// steps: the expected revision step on success (0 or 1); errIs: the expected error, nil = success.
	run := func(name string, c *clientv3.Client, tx func(clientv3.Txn) clientv3.Txn, errIs error, steps int64) *clientv3.TxnResponse {
		r0 := rev()
		resp, err := tx(c.Txn(ctx)).Commit()
		r1 := rev()
		t.Logf("CASE %-78s err=%v rev %d -> %d", name, err, r0, r1)
		if errIs == nil {
			require.NoError(t, err, name)
			require.Equal(t, r0+steps, r1, name)
			require.Equal(t, r1, resp.Header.Revision, name)
			return resp
		}
		require.Error(t, err, name)
		require.ErrorIs(t, err, errIs, name)
		require.Equal(t, r0, r1, name+": refused txn must not change the store")
		return nil
	}

	for i := 0; i < 3; i++ {
		alice := mk(i, "alice")
		wo := mk(i, "wo")
		p := fmt.Sprintf("m%d-", i)
		ka := func(s string) string { return "a/" + p + s }
		kc := func(s string) string { return "c/" + p + s }
		_, err := root.Put(ctx, kc("x"), "rootval")
		require.NoError(t, err)

		// 1. examples/etcd/auth's T4: a nested put outside the user's permission.
		run(p+"alice: T4 Then(OpTxn(nil,[Put c/..],nil))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(kc("t3"), "vt")}, nil))
		}, rpctypes.ErrPermissionDenied, 0)
		require.Equal(t, "<none>", val(kc("t3")))

		// 2. the same with a permitted put beside it: all or nothing.
		run(p+"alice: Then(Put a/.., OpTxn([Put c/..]))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut(ka("t2"), "v"), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(kc("t3"), "vt")}, nil))
		}, rpctypes.ErrPermissionDenied, 0)
		require.Equal(t, "<none>", val(ka("t2")))

		// 3. a refused nested put on the UNTAKEN outer branch (Else), the taken one permitted.
		run(p+"alice: Then(Put a/..) Else(OpTxn([Put c/..])), Then taken", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut(ka("t4"), "v")).Else(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(kc("t4"), "v")}, nil))
		}, rpctypes.ErrPermissionDenied, 0)
		// 4. a refused put in the UNTAKEN branch of a nested txn whose verdict is true.
		run(p+"alice: OpTxn(nil,[Put a/..],[Put c/..]) nested else untaken", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("t5"), "v")}, []clientv3.Op{clientv3.OpPut(kc("t5"), "v")}))
		}, rpctypes.ErrPermissionDenied, 0)
		// 5. a nested comparison on a key the user may not read (no write either).
		run(p+"alice: OpTxn(If(Value(c/x)=rootval),[Put a/..])", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn([]clientv3.Cmp{clientv3.Compare(clientv3.Value(kc("x")), "=", "rootval")}, []clientv3.Op{clientv3.OpPut(ka("t6"), "v")}, nil))
		}, rpctypes.ErrPermissionDenied, 0)
		// 6. write-only user: a nested comparison in its own range needs read.
		run(p+"wo: OpTxn(If(Version(a/..)=0),[Put a/..]) (write-only)", wo, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn([]clientv3.Cmp{clientv3.Compare(clientv3.Version(ka("t7")), "=", 0)}, []clientv3.Op{clientv3.OpPut(ka("t7"), "v")}, nil))
		}, rpctypes.ErrPermissionDenied, 0)
		run(p+"wo: OpTxn(nil,[Put a/..]) (write-only, no read needed)", wo, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("t7"), "v")}, nil))
		}, nil, 1)
		// 7. nested delete with PrevKv by the write-only user: needs read.
		run(p+"wo: OpTxn(nil,[Delete a/.. PrevKV])", wo, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete(ka("t7"), clientv3.WithPrevKV())}, nil))
		}, rpctypes.ErrPermissionDenied, 0)

		// 8. permitted nested txn: one revision step, the nested verdict in the response.
		r := run(p+"alice: Then(Put a/n1, OpTxn(nil,[Put a/n2],nil))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut(ka("n1"), "v1"), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("n2"), "v2")}, nil))
		}, nil, 1)
		require.True(t, r.Responses[1].GetResponseTxn().Succeeded)
		require.Equal(t, "v1", val(ka("n1")))
		require.Equal(t, "v2", val(ka("n2")))

		// 9. deep nesting (40 levels): refused outside, one step inside.
		run(p+"alice: 40-deep nested Put c/..", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(nest(40, clientv3.OpPut(kc("deep"), "v")))
		}, rpctypes.ErrPermissionDenied, 0)
		r = run(p+"alice: 40-deep nested Put a/..", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(nest(40, clientv3.OpPut(ka("deep"), "v")))
		}, nil, 1)
		require.Equal(t, "v", val(ka("deep")))
		d := r.Responses[0]
		for k := 0; k < 40; k++ {
			require.True(t, d.GetResponseTxn().Succeeded)
			d = d.GetResponseTxn().Responses[0]
		}
		require.NotNil(t, d.GetResponsePut())

		// 10. nested verdicts at the read state s0 (srvRunTxn), not after the outer put.
		_, err = alice.Put(ctx, ka("k"), "b")
		require.NoError(t, err)
		r = run(p+"alice: Then(Put a/k=x, OpTxn(If(Value(a/k)=x),[Put a/y=then],[Put a/y=else]))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut(ka("k"), "x"), clientv3.OpTxn([]clientv3.Cmp{clientv3.Compare(clientv3.Value(ka("k")), "=", "x")},
				[]clientv3.Op{clientv3.OpPut(ka("y"), "then")}, []clientv3.Op{clientv3.OpPut(ka("y"), "else")}))
		}, nil, 1)
		require.False(t, r.Responses[1].GetResponseTxn().Succeeded)
		require.Equal(t, "else", val(ka("y")))

		// 11. a nested get after the outer put reads the put (srvOps: in order).
		r = run(p+"alice: Then(Put a/g=v1, OpTxn(nil,[Get a/g]))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpPut(ka("g"), "v1"), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpGet(ka("g"))}, nil))
		}, nil, 1)
		g := r.Responses[1].GetResponseTxn().Responses[0].GetResponseRange()
		require.Len(t, g.Kvs, 1)
		require.Equal(t, "v1", string(g.Kvs[0].Value))

		// 12. a writing txn whose only operation is a nested txn of gets: through raft, no step.
		r = run(p+"alice: Then(OpTxn(nil,[Get a/g])) (not read-only, writes nothing)", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpGet(ka("g"))}, nil))
		}, nil, 0)
		require.Len(t, r.Responses[0].GetResponseTxn().Responses[0].GetResponseRange().Kvs, 1)

		// 13. the same key put in both branches of one nested txn: allowed (one runs).
		run(p+"alice: OpTxn(nil,[Put a/z=t],[Put a/z=e])", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("z"), "t")}, []clientv3.Op{clientv3.OpPut(ka("z"), "e")}))
		}, nil, 1)
		require.Equal(t, "t", val(ka("z")))

		// 14. sibling conflicts. A delete in an earlier nested sibling, a put in a later one: refused.
		run(p+"alice: Then(OpTxn([Delete a/s]), OpTxn([Put a/s]))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete(ka("s"))}, nil), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("s"), "v")}, nil))
		}, rpctypes.ErrDuplicateKey, 0)
		// a nested put and a top-level delete (either order): refused.
		run(p+"alice: Then(OpTxn([Put a/s]), Delete a/s)", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("s"), "v")}, nil), clientv3.OpDelete(ka("s")))
		}, rpctypes.ErrDuplicateKey, 0)
		run(p+"alice: Then(Delete a/s, OpTxn([Put a/s]))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpDelete(ka("s")), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("s"), "v")}, nil))
		}, rpctypes.ErrDuplicateKey, 0)
		// a put in an earlier nested sibling, a delete in a later one: ACCEPTED by etcd
		// (issues/etcd-txn-check-intervals-sibling.md); txnNestOk (txnSibSafeL) excludes it. The
		// state agrees with srvRunTxn's in-order run (the key ends deleted), one step.
		run(p+"alice: Then(OpTxn([Put a/s]), OpTxn([Delete a/s])) (excluded by txnNestOk)", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("s"), "v")}, nil), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpDelete(ka("s"))}, nil))
		}, nil, 1)
		require.Equal(t, "<none>", val(ka("s")))
		// two nested siblings putting one key: refused.
		run(p+"alice: Then(OpTxn([Put a/s]), OpTxn([Put a/s]))", alice, func(x clientv3.Txn) clientv3.Txn {
			return x.Then(clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("s"), "v")}, nil), clientv3.OpTxn(nil, []clientv3.Op{clientv3.OpPut(ka("s"), "w")}, nil))
		}, rpctypes.ErrDuplicateKey, 0)

		// 15. the raw request's shape: Txn's Then holds RequestOp_RequestTxn (not flattened).
		req := &pb.TxnRequest{Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestTxn{RequestTxn: &pb.TxnRequest{
			Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(kc("raw")), Value: []byte("v")}}}}}}}}}
		_, err = integration.ToGRPC(alice).KV.Txn(ctx, req)
		t.Logf("CASE %-78s err=%v", p+"alice: raw gRPC nested put c/..", err)
		require.ErrorIs(t, err, rpctypes.ErrGRPCPermissionDenied)
		require.Equal(t, "<none>", val(kc("raw")))
	}
}
