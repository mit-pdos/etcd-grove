// Package clientv3kv holds the requirement snippets of etcd's Go client KV API (batch W0,
// Spec/go_etcd_io/etcd/client/v3/): minimal uses of the patterns the client's users rely on
// (client/v3/concurrency, leasing, recipes, the cache, Kubernetes' etcd3 store, this repository's
// examples), each reliance an explicit panic.
//
// Common assumptions (the proofs' setting): cli is a client of a cluster (isClient), the caller
// owns the cluster's state etcdState in an invariant of its own (the "owner's invariant"), and
// the keys a snippet names as "owned" are written by no other principal (an invariant clause the
// owner keeps: every update fired through the invariant is checked against it) and attached to
// no lease (so the environment's lease expiry does not delete them). Contexts are any contexts
// that carry no auth token metadata of their own (ctxPrin: Background, TODO, their children,
// WithRequireLeader's).
package clientv3kv

import (
	"bytes"
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3kv/put-then-get: a read after an acknowledged write sees it, at a revision at least
// the write's; the key's mod revision is the write's revision.
// Users: examples/etcd/txnlin/linkvtxn.go:874,837 (callPut, callGet: porcupine checks exactly this),
// examples/etcd/putget, client/v3/concurrency/stm.go (reads its own commits), Kubernetes' store
// (a Get after an OptimisticPut).
// Assumes: k is owned (see the package comment).
// Specs: Client.Put.spec, Client.Get.spec (KV.PutTriple, KV.GetTriple); laws: etcdState_lb,
// etcdLb_reach, etcdState_revFits, rangeRespOwn_unfold, keyValueOwn_unfold.
func ReqPutThenGet(ctx context.Context, cli *clientv3.Client, k, v string) {
	presp, err := cli.Put(ctx, k, v)
	if err != nil {
		return
	}
	gresp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if len(gresp.Kvs) != 1 {
		panic("put-then-get: lost write")
	}
	kv := gresp.Kvs[0]
	if !bytes.Equal(kv.Value, []byte(v)) {
		panic("put-then-get: wrong value")
	}
	if kv.ModRevision != presp.Header.Revision {
		panic("put-then-get: wrong mod revision")
	}
	if gresp.Header.Revision < presp.Header.Revision {
		panic("put-then-get: revision went back")
	}
}

// REQ clientv3kv/put-revision: a put's reply carries the new revision, above every revision
// the caller saw before; with WithPrevKV, the previous key-value (the caller's own put, at its
// reply's revision).
// Users: client/v3/concurrency/election.go (Proclaim's revision), Kubernetes' store (the
// resourceVersion of a write is the reply's revision), examples/etcd/compacted.
// Assumes: k is owned; prevRev is the header revision of an earlier reply of this client.
// Specs: Client.Put.spec, WithPrevKV.spec; laws: putRespOwn_unfold, etcdLb_reach.
func ReqPutRevision(ctx context.Context, cli *clientv3.Client, k string, prevRev int64) {
	r1, err := cli.Put(ctx, k, "a")
	if err != nil {
		return
	}
	if r1.Header.Revision <= prevRev {
		panic("put-revision: not a new revision")
	}
	r2, err := cli.Put(ctx, k, "b", clientv3.WithPrevKV())
	if err != nil {
		return
	}
	if r2.PrevKv == nil || !bytes.Equal(r2.PrevKv.Value, []byte("a")) {
		panic("put-revision: wrong previous key-value")
	}
	if r2.PrevKv.ModRevision != r1.Header.Revision || r2.Header.Revision <= r1.Header.Revision {
		panic("put-revision: wrong revisions")
	}
}

// REQ clientv3kv/delete-then-get: a delete removes the key; its reply counts it.
// Users: client/v3/concurrency/mutex.go:118 (Unlock), recipes/rwmutex.go, examples/etcd/txnlin
// (callDel), Kubernetes' store (deletes through a transaction).
// Assumes: k is owned and was put by this caller.
// Specs: Client.Delete.spec, Client.Get.spec; laws: deleteRespOwn_unfold.
func ReqDeleteThenGet(ctx context.Context, cli *clientv3.Client, k string) {
	if _, err := cli.Put(ctx, k, "v"); err != nil {
		return
	}
	dresp, err := cli.Delete(ctx, k)
	if err != nil {
		return
	}
	if dresp.Deleted != 1 {
		panic("delete: wrong count")
	}
	gresp, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if len(gresp.Kvs) != 0 || gresp.Count != 0 {
		panic("delete-then-get: key still there")
	}
}

// REQ clientv3kv/list-prefix: a prefix read returns the keys of the prefix in key order, and
// Count counts them all even when a limit cuts the list (More set).
// Users: client/v3/concurrency (waitDeletes), recipes (queue, barrier), the cache (cache.go Get
// with WithPrefix, WithLimit), Kubernetes' store (GetList with WithRange, WithLimit).
// Assumes: none (any concurrent writers).
// Specs: Client.Get.spec, WithPrefix.spec, WithLimit.spec; the model's RangeReq.answers; law
// etcdState_sizeFits (Count fits an int64).
func ReqListPrefix(ctx context.Context, cli *clientv3.Client, pfx string) {
	resp, err := cli.Get(ctx, pfx, clientv3.WithPrefix(), clientv3.WithLimit(2))
	if err != nil {
		return
	}
	if len(resp.Kvs) > 2 {
		panic("list: limit exceeded")
	}
	if resp.More != (resp.Count > int64(len(resp.Kvs))) {
		panic("list: More disagrees with Count")
	}
	if resp.More && len(resp.Kvs) == 0 {
		// client/v3/mirror/syncer.go pages from the last key when More is set
		panic("list: More with an empty page")
	}
	for i, kv := range resp.Kvs {
		if !bytes.HasPrefix(kv.Key, []byte(pfx)) {
			panic("list: key outside the prefix")
		}
		if i > 0 && bytes.Compare(resp.Kvs[i-1].Key, kv.Key) >= 0 {
			panic("list: not in key order")
		}
	}
}
