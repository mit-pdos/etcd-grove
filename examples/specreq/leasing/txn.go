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
	resp, err := lkv.Do(ctx, clientv3.OpGet(k, clientv3.WithSerializable()))
	if err != nil {
		return
	}
	if resp.Get() == nil {
		panic("do-proxy-range: no range reply")
	}
}

// REQ leasing/do-txn: the proxy's Txn: Do of OpTxn over slices of exactly their length, whose
// branches are not transactions, returns a transaction reply on success.
// Users: server/proxy/grpcproxy/kv.go:116 (TxnRequestToOp).
// Assumes: the common assumptions.
// Specs: leasingKV.Do.spec (flatTxn), OpTxn.spec, Compare.spec, ModRevision.spec.
func ReqDoTxn(ctx context.Context, lkv clientv3.KV, k, v string, rev int64) {
	cmps := []clientv3.Cmp{clientv3.Compare(clientv3.ModRevision(k), "=", rev)}
	thenOps := []clientv3.Op{clientv3.OpPut(k, v)}
	elseOps := []clientv3.Op{clientv3.OpGet(k)}
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
