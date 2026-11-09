package leasing

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ leasing/put-revision: a put's reply revision is reached: a later plain read is at a
// revision at least it, and sees the value (k owned: every application of this put wrote v).
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingPutGet,
// TestLeasingOwnerPutResponse); the proxy's Put.
// Assumes: the common assumptions; k owned.
// Specs: leasingKV.Put.spec (LKV.PutTriple, putReplyL), Client.Get.spec; laws: putRespOwn_unfold,
// etcdLb_reach.
func ReqPutRevision(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k, v string) {
	presp, err := lkv.Put(ctx, k, v)
	if err != nil {
		return
	}
	gresp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if gresp.Header.Revision < presp.Header.Revision {
		panic("put-revision: revision went back")
	}
	if len(gresp.Kvs) != 1 || string(gresp.Kvs[0].Value) != v {
		panic("put-revision: lost write")
	}
}

// REQ leasing/put-error: an error settles nothing: the caller retries or gives up.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingOwnerPutError,
// TestLeasingNonOwnerPutError); the proxy (returns it).
// Assumes: the common assumptions.
// Specs: leasingKV.Put.spec (the error disjunct).
func ReqPutError(ctx context.Context, lkv clientv3.KV, k, v string) error {
	if _, err := lkv.Put(ctx, k, v); err != nil {
		return err
	}
	return nil
}

// REQ leasing/delete-then-plain-get: after a delete through the leasing KV, a plain read finds
// the key gone.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingDeleteOwner,
// TestLeasingDeleteNonOwner); the proxy's DeleteRange.
// Assumes: the common assumptions; k owned.
// Specs: leasingKV.Delete.spec (LKV.DeleteTriple), Client.Get.spec; laws: etcdLb_reach.
func ReqDeleteThenPlainGet(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k string) {
	if _, err := lkv.Delete(ctx, k); err != nil {
		return
	}
	gresp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if len(gresp.Kvs) != 0 {
		panic("delete-then-plain-get: key still there")
	}
}

// REQ leasing/compact: Compact goes to the cluster as through the plain client.
// Users: server/proxy/grpcproxy/kv.go:144.
// Assumes: the common assumptions; rev ≠ 0.
// Specs: leasingKV.Compact.spec (W0's KV.CompactTriple).
func ReqCompactThroughLeasing(ctx context.Context, lkv clientv3.KV, rev int64) {
	if rev == 0 {
		return
	}
	_, _ = lkv.Compact(ctx, rev)
}
