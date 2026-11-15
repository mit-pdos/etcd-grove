package leasing

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ leasing/do-proxy-range: the proxy's Range: Do of a get with its options returns a range
// reply (Get() non-nil) on success.
// Users: server/proxy/grpcproxy/kv.go:62 (RangeRequestToOp).
// Assumes: the common assumptions.
// Specs: leasingKV.Do.spec (LKV.DoTriple, doReplyL), OpGet.spec, WithSerializable.spec; laws:
// msgOwn_ne_null.
func ReqDoProxyRange(ctx context.Context, lkv clientv3.KV, k string) {
	// as RangeRequestToOp builds it, from a request with zero fields but serializable
	op := clientv3.OpGet(k, clientv3.WithRev(0), clientv3.WithLimit(0),
		clientv3.WithSort(clientv3.SortByKey, clientv3.SortNone),
		clientv3.WithMaxCreateRev(0), clientv3.WithMinCreateRev(0),
		clientv3.WithMaxModRev(0), clientv3.WithMinModRev(0), clientv3.WithSerializable())
	resp, err := lkv.Do(ctx, op)
	if err != nil {
		return
	}
	if resp.Get() == nil {
		panic("do-proxy-range: no range reply")
	}
}

// REQ leasing/do-put-delete: the proxy's Put and DeleteRange: Do of OpPut (with its options) and
// of OpDelete returns a put reply (Put() non-nil) and a delete reply (Del() non-nil) on success.
// Users: server/proxy/grpcproxy/kv.go:86 (PutRequestToOp), :94 (DelRequestToOp).
// Assumes: the common assumptions.
// Specs: leasingKV.Do.spec (LKV.DoTriple, doReplyL), OpPut.spec, OpDelete.spec, WithPrevKV.spec;
// laws: msgOwn_ne_null.
func ReqDoPutDelete(ctx context.Context, lkv clientv3.KV, k, v string) {
	// as PutRequestToOp and DelRequestToOp build them, from requests asking for the previous kv
	presp, err := lkv.Do(ctx, clientv3.OpPut(k, v, clientv3.WithPrevKV()))
	if err != nil {
		return
	}
	if presp.Put() == nil {
		panic("do-put-delete: no put reply")
	}
	dresp, err := lkv.Do(ctx, clientv3.OpDelete(k, clientv3.WithPrevKV()))
	if err != nil {
		return
	}
	if dresp.Del() == nil {
		panic("do-put-delete: no delete reply")
	}
}

// REQ leasing/do-txn: the proxy's Txn: Do of OpTxn over slices of exactly their length, nested
// transactions included, returns a transaction reply on success.
// Users: server/proxy/grpcproxy/kv.go:116 (TxnRequestToOp).
// Assumes: the common assumptions.
// Assumes (also): k marked (lkvClean_mark).
// Specs: leasingKV.Do.spec (opCapOk: opCapOk_intro over the make'd slices), OpTxn.spec,
// Compare.spec, ModRevision.spec.
func ReqDoTxn(ctx context.Context, lkv clientv3.KV, k, v string, rev int64) {
	// as TxnRequestToOp builds it: slices of exactly their length, a nested transaction
	inner := make([]clientv3.Op, 1)
	inner[0] = clientv3.OpGet(k)
	cmps := make([]clientv3.Cmp, 1)
	cmps[0] = clientv3.Compare(clientv3.ModRevision(k), "=", rev)
	thenOps := make([]clientv3.Op, 2)
	thenOps[0] = clientv3.OpPut(k, v)
	thenOps[1] = clientv3.OpTxn(nil, inner, make([]clientv3.Op, 0))
	elseOps := make([]clientv3.Op, 1)
	elseOps[0] = clientv3.OpGet(k)
	resp, err := lkv.Do(ctx, clientv3.OpTxn(cmps, thenOps, elseOps))
	if err != nil {
		return
	}
	if resp.Txn() == nil {
		panic("do-txn: no transaction reply")
	}
}

// REQ leasing/txn-cas: a compare-and-swap through the leasing Txn builder: a reply with a header
// on success.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingTxnOwnerIf,
// TestLeasingTxnRandIfThenOrElse).
// Assumes: the common assumptions.
// Assumes (also): k marked (lkvClean_mark).
// Specs: leasingKV.Txn.spec, txnLeasing.{If,Then,Else,Commit}.spec (LTxn.*Triple, txnReplyL).
func ReqTxnCAS(ctx context.Context, lkv clientv3.KV, k, v string, rev int64) {
	resp, err := lkv.Txn(ctx).
		If(clientv3.Compare(clientv3.ModRevision(k), "=", rev)).
		Then(clientv3.OpPut(k, v)).
		Else(clientv3.OpGet(k)).
		Commit()
	if err != nil {
		return
	}
	if resp.Header == nil {
		panic("txn-cas: no header")
	}
}

// REQ leasing/txn-read-only: a read-only transaction (possibly answered from the cache) has a
// header at a revision the cluster reached.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingTxnOwnerGet,
// TestLeasingTxnAtomicCache).
// Assumes: the common assumptions.
// Specs: txnLeasing.Commit.spec (CachedAns: rev ≤ σ.kv.rev), Client.Get.spec; laws: etcdLb_reach.
func ReqTxnReadOnly(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k string) {
	resp, err := lkv.Txn(ctx).Then(clientv3.OpGet(k)).Commit()
	if err != nil {
		return
	}
	g, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if g.Header.Revision < resp.Header.Revision {
		panic("txn-read-only: a revision the cluster never reached")
	}
}

// REQ leasing/txn-positional: a transaction's responses are, by position, of the kinds of the
// branch it reports (the proxy's txnToCache dereferences them so).
// Users: server/proxy/grpcproxy/kv.go:99-113 (txnToCache).
// Assumes: the common assumptions; k1 marked (lkvClean_mark).
// Specs: txnLeasing.Commit.spec (txnReplyL: ofResps of the branch; CachedAns: a branch of ranges
// only, so not the then-branch with its put); laws: txnRespOwn_unfold, responseOpOwn_unfold.
func ReqTxnPositional(ctx context.Context, lkv clientv3.KV, k1, k2 string, rev int64) {
	resp, err := lkv.Txn(ctx).
		If(clientv3.Compare(clientv3.ModRevision(k1), "=", rev)).
		Then(clientv3.OpPut(k1, "v"), clientv3.OpGet(k2)).
		Else(clientv3.OpGet(k1)).
		Commit()
	if err != nil {
		return
	}
	if resp.Succeeded {
		if len(resp.Responses) != 2 || resp.Responses[0].GetResponsePut() == nil ||
			resp.Responses[1].GetResponseRange() == nil {
			panic("txn-positional: then-branch responses")
		}
	} else if len(resp.Responses) != 1 || resp.Responses[0].GetResponseRange() == nil {
		panic("txn-positional: else-branch responses")
	}
}

// REQ leasing/one-client-both-kvs: one function serves a plain KV and a leasing KV alike (the
// proxy's kvProxy, with or without --experimental-leasing-prefix).
// Users: server/proxy/grpcproxy/kv.go (NewKvProxy over client.KV).
// Assumes: the common assumptions; kv meets W0's KV contract (kvAt_lkvAt, lkvAlloc) or is a
// leasing KV (NewKV.spec).
// Specs: lkvAt_methods (LKV.DoTriple), kvAt_lkvAt, lkvAlloc.
func ReqOneClientBothKVs(ctx context.Context, kv clientv3.KV, k string) {
	resp, err := kv.Do(ctx, clientv3.OpGet(k))
	if err != nil {
		return
	}
	if resp.Get() == nil {
		panic("one-client-both-kvs: no range reply")
	}
}
