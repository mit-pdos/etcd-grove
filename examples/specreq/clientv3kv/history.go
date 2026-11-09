package clientv3kv

import (
	"bytes"
	"context"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3kv/get-at-revision: a get at a revision the caller saw returns what the key held
// then (unless that revision is compacted), whichever member answers and whatever was written
// since: the history is the cluster's.
// Users: Kubernetes' store (Get and GetList at a resourceVersion: revread_test.go,
// examples/k8s/etcd3), client/v3/concurrency/stm.go (stmRepeatable's reads at the first read's
// revision), the cache (cache.go Get WithRev inside its window), leasing (reads at a revision).
// Assumes: k is owned (see the package comment).
// Specs: Client.Put.spec, Client.Get.spec, WithRev.spec; the model's KVHist.storeAt (the whole
// history is kept, the compaction revision only refuses reads); laws: etcdState_lb, etcdLb_reach.
func ReqGetAtRevision(ctx context.Context, cli *clientv3.Client, k string) {
	p, err := cli.Put(ctx, k, "old")
	if err != nil {
		return
	}
	if _, err := cli.Put(ctx, k, "new"); err != nil {
		return
	}
	g, err := cli.Get(ctx, k, clientv3.WithRev(p.Header.Revision))
	if err == rpctypes.ErrCompacted {
		return
	}
	if err != nil {
		return
	}
	if len(g.Kvs) != 1 || !bytes.Equal(g.Kvs[0].Value, []byte("old")) {
		panic("get-at-revision: the value at that revision")
	}
}

// REQ clientv3kv/compact-reached: a compaction at a revision the cluster reached is never
// ErrFutureRev, and after it a read below that revision is ErrCompacted; another compactor may
// have gone further (ErrCompacted), and the server's own auto-compaction may run at any time.
// Users: Kubernetes' compactor (etcd3/compact.go:220,269: a compare-and-swap of compact_rev_key,
// then Compact at the transaction's revision), the cache (cache/demux.go), the examples
// (examples/etcd/compacted, compactwatch).
// Assumes: none (other compactors and the server's auto-compaction allowed).
// Specs: Client.Txn.spec ..., Client.Compact.spec (rev ≠ 0: the transaction's revision is at
// least 1), Client.Get.spec, Version.spec; the model's kvStep (.compact), EnvStep.compact; laws:
// etcdLb_reach.
func ReqCompactReached(ctx context.Context, cli *clientv3.Client, key string, t int64) {
	resp, err := cli.Txn(ctx).
		If(clientv3.Compare(clientv3.Version(key), "=", t)).
		Then(clientv3.OpPut(key, "")).
		Else(clientv3.OpGet(key)).
		Commit()
	if err != nil {
		return
	}
	rev := resp.Header.Revision
	if rev < 1 {
		panic("compact: a revision is at least 1")
	}
	_, err = cli.Compact(ctx, rev)
	if err == rpctypes.ErrFutureRev {
		panic("compact: the transaction's revision was reached")
	}
	if err != nil {
		return
	}
	if rev > 1 {
		_, err = cli.Get(ctx, key, clientv3.WithRev(rev-1))
		if err == nil {
			panic("compact: a read below the compaction revision is refused")
		}
	}
}

// REQ clientv3kv/revisions-monotone: the revisions a client reads never go back, whichever
// member answers a linearizable read.
// Users: Kubernetes' watch cache and store (resourceVersions only grow), the cache (its
// window), examples/etcd/txnlin (porcupine's model checks it).
// Assumes: none.
// Specs: Client.Get.spec; laws: etcdState_lb, etcdLb_reach, etcdLb_ord.
func ReqRevisionsMonotone(ctx context.Context, cli *clientv3.Client, k string) {
	a, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	b, err := cli.Get(ctx, k)
	if err != nil {
		return
	}
	if b.Header.Revision < a.Header.Revision {
		panic("revisions went back")
	}
}
