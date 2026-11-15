package clientv3kv

import (
	"bytes"
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3kv/cas-mod-revision: a compare-and-swap on the mod revision: when it succeeds the
// put took the transaction's revision; when it fails the else-branch's get shows a mod revision
// other than the expected one (both branches see one state).
// Users: Kubernetes' store (OptimisticPut through client/v3/kubernetes: If(ModRevision(key) =
// rv).Then(OpPut(...)).Else(OpGet(key))), client/v3/concurrency/stm.go:203 (commit: If(the
// read set's mod revisions).Then(the write set)), recipes/key.go (putNewKV: If(ModRevision = 0)).
// Assumes: none (any concurrent writers).
// Specs: Client.Txn.spec, txn.If.spec, txn.Then.spec, txn.Else.spec, txn.Commit.spec (the Txn
// contract), Compare.spec, ModRevision.spec, OpPut.spec, OpGet.spec; ResponseOp.GetResponseRange
// (3h, req/go_etcd_io_etcd_api_v3_etcdserverpb.md); laws: txnRespOwn_unfold, responseOpOwn_unfold.
func ReqCASModRevision(ctx context.Context, cli *clientv3.Client, k string, rev int64, v string) {
	resp, err := cli.Txn(ctx).
		If(clientv3.Compare(clientv3.ModRevision(k), "=", rev)).
		Then(clientv3.OpPut(k, v)).
		Else(clientv3.OpGet(k)).
		Commit()
	if err != nil {
		return
	}
	if len(resp.Responses) != 1 {
		panic("cas: one response per operation of the branch")
	}
	if resp.Succeeded {
		if resp.Responses[0].GetResponsePut() == nil {
			panic("cas: the then-branch answers a put")
		}
		return
	}
	rr := resp.Responses[0].GetResponseRange()
	if rr == nil {
		panic("cas: the else-branch answers a get")
	}
	if len(rr.Kvs) == 1 && rr.Kvs[0].ModRevision == rev {
		panic("cas: failed compare but the revision matches")
	}
	if len(rr.Kvs) == 0 && rev == 0 {
		panic("cas: a missing key compares as revision 0")
	}
}

// REQ clientv3kv/create-if-absent: a creation guarded by CreateRevision = 0, with a lease; on
// success the key is the caller's (its create revision is the transaction's); on failure the
// else-branch shows the owner's key.
// Users: client/v3/concurrency/mutex.go:83 (tryAcquire), election.go:69 (Campaign),
// recipes/key.go (putNewKV), leasing/txn.go (its ownership keys).
// Assumes: lease is a lease the caller granted (it may have expired: ErrLeaseNotFound is a
// linearized answer, no panic).
// Specs: as ReqCASModRevision, CreateRevision.spec, WithLease.spec.
func ReqCreateIfAbsent(ctx context.Context, cli *clientv3.Client, k string, lease clientv3.LeaseID) {
	resp, err := cli.Txn(ctx).
		If(clientv3.Compare(clientv3.CreateRevision(k), "=", 0)).
		Then(clientv3.OpPut(k, "", clientv3.WithLease(lease))).
		Else(clientv3.OpGet(k)).
		Commit()
	if err != nil {
		return
	}
	if !resp.Succeeded {
		rr := resp.Responses[0].GetResponseRange()
		if rr == nil || len(rr.Kvs) != 1 {
			panic("create-if-absent: the else-branch shows the existing key")
		}
		if rr.Kvs[0].CreateRevision == 0 || rr.Kvs[0].CreateRevision > resp.Header.Revision {
			panic("create-if-absent: the existing key's create revision")
		}
	}
}

// REQ clientv3kv/txn-reads-own-writes: inside one transaction, a get after a put of the same
// key sees the put, at the transaction's revision.
// Users: leasing/txn.go (gets after puts in one commit), examples/etcd/txnlin (multi-operation
// transactions: callTxn with up to three operations).
// Assumes: none.
// Specs: as ReqCASModRevision; the model's TxnRun.
func ReqTxnReadsOwnWrites(ctx context.Context, cli *clientv3.Client, k string) {
	resp, err := cli.Txn(ctx).Then(clientv3.OpPut(k, "x"), clientv3.OpGet(k)).Commit()
	if err != nil {
		return
	}
	if !resp.Succeeded {
		panic("txn: no comparison, the then-branch")
	}
	rr := resp.Responses[1].GetResponseRange()
	if rr == nil || len(rr.Kvs) != 1 || !bytes.Equal(rr.Kvs[0].Value, []byte("x")) {
		panic("txn: a get after a put in one transaction sees it")
	}
	if rr.Kvs[0].ModRevision != resp.Header.Revision {
		panic("txn: the put took the transaction's revision")
	}
}

// REQ clientv3kv/txn-nested-range-headers: a transaction's nested ranges carry a header whose
// revision is the transaction's read revision (the outer header's, before any write).
// Users: client/v3/concurrency/stm.go:193,201,293,325 (it keeps the nested range responses as
// GetResponses and pins its later reads at their Header.Revision).
// Assumes: none.
// Specs: Client.Txn.spec ..., txn.Commit.spec; the model's TxnRun (.range rev), Wire's
// ResponseOpM.ofResp.
func ReqTxnNestedRangeHeaders(ctx context.Context, cli *clientv3.Client, k1, k2 string) {
	resp, err := cli.Txn(ctx).Then(clientv3.OpGet(k1), clientv3.OpGet(k2)).Commit()
	if err != nil {
		return
	}
	for _, r := range resp.Responses {
		rr := r.GetResponseRange()
		if rr == nil || rr.Header == nil || rr.Header.Revision != resp.Header.Revision {
			panic("txn: a nested range's header is the transaction's read revision")
		}
	}
}

// REQ clientv3kv/txn-nested: a nested transaction's branch is decided by its own comparisons,
// evaluated before the outer transaction's writes.
// Users: leasing/txn.go (OpTxn of the user's transaction inside its own guard).
// Assumes: k is owned, holds "a" and is attached to no lease.
// Specs: OpTxn.spec, Value.spec, txn.Commit.spec; ResponseOp.GetResponseTxn (3h).
func ReqTxnNested(ctx context.Context, cli *clientv3.Client, k string) {
	inner := clientv3.OpTxn(
		[]clientv3.Cmp{clientv3.Compare(clientv3.Value(k), "=", "a")},
		[]clientv3.Op{clientv3.OpGet(k)}, nil)
	resp, err := cli.Txn(ctx).Then(clientv3.OpPut(k, "b"), inner).Commit()
	if err != nil {
		return
	}
	tr := resp.Responses[1].GetResponseTxn()
	if tr == nil || !tr.Succeeded {
		panic("txn-nested: the nested comparison sees the state before the transaction")
	}
}

// REQ clientv3kv/txn-readonly-serializable: a read-only transaction whose gets are all
// serializable (the empty one included) is answered from one member's possibly stale view: no
// lower bound on its revision, nothing to panic on but the shape.
// Users: client/v3/concurrency/stm.go (stmSerializable's prefetch), etcdctl txn with --consistency=s.
// Assumes: none.
// Specs: txn.Commit.spec with a persistent update (Req.isRead); the model's kvStep (.txn), its
// view (issues/etcd-txn-empty-serializable.md).
func ReqTxnReadonlySerializable(ctx context.Context, cli *clientv3.Client, k string) {
	resp, err := cli.Txn(ctx).If(clientv3.Compare(clientv3.Version(k), "=", 0)).Commit()
	if err != nil {
		return
	}
	if len(resp.Responses) != 0 {
		panic("txn: no operation, no response")
	}
	if resp.Header.Revision < 1 {
		panic("txn: a revision is at least 1")
	}
}
