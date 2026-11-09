package leasing

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ leasing/get-key: a Get of one key answers about that key only (at most one key-value, of
// that key), with a header.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingPutGet, TestLeasingInterval);
// the proxy's Range (through Do).
// Assumes: the common assumptions.
// Specs: leasingKV.Get.spec (LKV.GetTriple: a member's answer, or CachedAns); laws:
// rangeRespOwn_unfold, keyValueOwn_unfold.
func ReqGetKey(ctx context.Context, lkv clientv3.KV, k string) {
	resp, err := lkv.Get(ctx, k)
	if err != nil {
		return
	}
	if resp.Header == nil {
		panic("get-key: no header")
	}
	if len(resp.Kvs) > 1 {
		panic("get-key: more than one key-value")
	}
	if len(resp.Kvs) == 1 && string(resp.Kvs[0].Key) != k {
		panic("get-key: another key")
	}
}

// REQ leasing/get-then-plain-get: a Get's header revision is one the cluster reached: a later
// read through the plain client is at a revision at least it.
// Users: the proxy's clients (revisions they carry between calls).
// Assumes: the common assumptions.
// Specs: leasingKV.Get.spec (CachedRange: rev ≤ σ.kv.rev), Client.Get.spec; laws: etcdState_lb,
// etcdLb_reach (revisions only grow along Reach).
func ReqGetThenPlainGet(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k string) {
	r1, err := lkv.Get(ctx, k)
	if err != nil {
		return
	}
	r2, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if r2.Header.Revision < r1.Header.Revision {
		panic("get-then-plain-get: a revision the cluster never reached")
	}
}

// REQ leasing/getstream-unsupported: GetStream through a leasing KV may be called; it fails with
// an error that settles nothing (the code always fails).
// Users: none (a caller of the KV interface).
// Assumes: the common assumptions.
// Specs: leasingKV.GetStream.spec (W0's KV.GetStreamTriple).
func ReqGetStreamUnsupported(ctx context.Context, lkv clientv3.KV, k string) {
	ch, err := lkv.GetStream(ctx, k)
	if err != nil {
		return
	}
	for range ch {
	}
}

// REQ leasing/cached-read-unwritten: a key never written through the leasing KV is read as some
// past state of the cluster had it (W0's serializable answer), cached or not.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingGetSerializable,
// TestLeasingOverwriteResponse); the proxy's read-only users (the watch proxy's permission check,
// /health).
// Assumes: the common assumptions; k owned, absent before, written only by this plain put; the
// program keeps lkvClean of k (never marks it).
// Specs: Client.Put.spec, leasingKV.Get.spec (CachedRange1: CachedSer or a plain get's, the key
// unmarked: lkvClean_marks); laws: etcdLb_reach.
func ReqCachedReadUnwritten(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k string) {
	if _, err := cli.Put(ctx, k, "abc"); err != nil {
		return
	}
	for i := 0; i < 2; i++ {
		g, err := lkv.Get(ctx, k)
		if err != nil {
			return
		}
		if len(g.Kvs) == 1 && string(g.Kvs[0].Value) != "abc" {
			panic("cached-read-unwritten: a value the key never had")
		}
	}
}

// REQ leasing/get-prefix: a prefix Get is never served from the cache: after acknowledged puts of
// owned keys under the prefix, it returns all of them.
// Users: tests/integration/clientv3/lease/leasing_test.go (TestLeasingInterval,
// TestLeasingTxnOwnerGetRange); the proxy's ranges; endpoints.Manager's prefix Get then watch.
// Assumes: the common assumptions; every key under p owned, only these two put.
// Specs: Client.Put.spec, leasingKV.Get.spec (CachedRange1 needs no range end: the answer is a Step).
func ReqGetPrefix(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, p string) {
	if _, err := cli.Put(ctx, p+"a", "1"); err != nil {
		return
	}
	if _, err := cli.Put(ctx, p+"b", "2"); err != nil {
		return
	}
	g, err := lkv.Get(ctx, p, clientv3.WithPrefix())
	if err != nil {
		return
	}
	if len(g.Kvs) != 2 {
		panic("get-prefix: a key missing")
	}
}
