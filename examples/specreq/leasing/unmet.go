package leasing

// The requirements the KV contract's users (the proxy's clients, the integration tests) have of
// the leasing KV that the pinned code violates. Each panic is reachable (its issue has a failing
// test, or the header says how); no spec of this batch gives them, and their snippets are NOT
// claimed provable. They record what the leasing contract's weakenings cost (Api.lean's header).

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// UNMET leasing/put-once: a put of a fresh key leaves it at version 1.
// Violated: issues/leasing-modify-uncached-once.md (applied twice: version 2).
// Assumes: k owned and absent; no other leasing client.
func UnmetPutOnce(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k string) {
	if _, err := lkv.Put(ctx, k, "v"); err != nil {
		return
	}
	g, err := cli.Get(ctx, k)
	if err != nil || len(g.Kvs) != 1 {
		return
	}
	if g.Kvs[0].Version != 1 {
		panic("put-once: applied more than once")
	}
}

// UNMET leasing/read-your-write-across: a write through another leasing KV (or the plain client)
// is seen by a later Get of this one.
// Violated: the lease-expiry window (no time model; etcd-io/etcd#19091),
// issues/leasing-stale-entry-after-reset.md, and any plain-client writer (the protocol fences
// only leasing writers).
// Assumes: k owned by this program.
func UnmetReadAcross(ctx context.Context, lkv1, lkv2 clientv3.KV, k, v string) {
	if _, err := lkv1.Get(ctx, k); err != nil {
		return
	}
	if _, err := lkv2.Put(ctx, k, v); err != nil {
		return
	}
	g, err := lkv1.Get(ctx, k)
	if err != nil {
		return
	}
	if len(g.Kvs) != 1 || string(g.Kvs[0].Value) != v {
		panic("read-across: stale cached value")
	}
}

// UNMET leasing/revisions-monotone: a Get's header revision is at least one this client saw
// before (W0's ReqRevisionsMonotone).
// Violated: a cached Get answers with the entry's header (cache.go: copyGetResponseMetadataOnly),
// older than revisions seen since (req/go_etcd_io_etcd_client_v3_leasing.md, from W0).
func UnmetRevisionsMonotone(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k, other string) {
	if _, err := lkv.Get(ctx, k); err != nil {
		return
	}
	p, err := cli.Put(ctx, other, "x")
	if err != nil {
		return
	}
	g, err := lkv.Get(ctx, k)
	if err != nil {
		return
	}
	if g.Header.Revision < p.Header.Revision {
		panic("revisions-monotone: header revision went back")
	}
}

// UNMET leasing/get-options: a keys-only Get returns no value.
// Violated: issues/leasing-get-failed-acquire-options.md (another leasing client holds k).
func UnmetGetOptions(ctx context.Context, lkv clientv3.KV, k string) {
	g, err := lkv.Get(ctx, k, clientv3.WithKeysOnly())
	if err != nil {
		return
	}
	for _, kv := range g.Kvs {
		if len(kv.Value) != 0 {
			panic("get-options: keys-only Get returned a value")
		}
	}
}

// UNMET leasing/delete-range-prevkv: a range delete WithPrevKV returns the deleted key-values.
// Violated: deleteRangeRPC drops the option (a finding of batch 1e, by code reading).
// Assumes: pfx has exactly one key, owned.
func UnmetDeleteRangePrevKV(ctx context.Context, lkv clientv3.KV, pfx string) {
	d, err := lkv.Delete(ctx, pfx, clientv3.WithPrefix(), clientv3.WithPrevKV())
	if err != nil {
		return
	}
	if d.Deleted == 1 && len(d.PrevKvs) != 1 {
		panic("delete-range-prevkv: previous key-values dropped")
	}
}

// UNMET leasing/txn-missing-key: a transaction compares a missing key as etcd does.
// Violated: issues/leasing-evalcmp-missing-key.md (k cached as missing: Succeeded false).
// Assumes: k owned and absent.
func UnmetTxnMissingKey(ctx context.Context, lkv clientv3.KV, k string) {
	if _, err := lkv.Get(ctx, k); err != nil {
		return
	}
	t, err := lkv.Txn(ctx).If(clientv3.Compare(clientv3.CreateRevision(k), "<", 5)).
		Then(clientv3.OpGet(k)).Commit()
	if err != nil {
		return
	}
	if !t.Succeeded {
		panic("txn-missing-key: wrong branch")
	}
}

// UNMET leasing/sequential-puts: after two acknowledged puts of one key, the second's value stays.
// Violated: nonissues/leasing-write-resend-after-error.md (the first put's first attempt, failed
// with an error that settles nothing, lands after its resend succeeded and after the second put).
// Assumes: k owned.
func UnmetSequentialPuts(ctx context.Context, cli *clientv3.Client, lkv clientv3.KV, k string) {
	if _, err := lkv.Put(ctx, k, "v1"); err != nil {
		return
	}
	if _, err := lkv.Put(ctx, k, "v2"); err != nil {
		return
	}
	g, err := cli.Get(ctx, k)
	if err != nil || len(g.Kvs) != 1 {
		return
	}
	if string(g.Kvs[0].Value) != "v2" {
		panic("sequential-puts: an earlier write landed late")
	}
}

// UNMET leasing/txn-atomic-cache: a cached read-only transaction reads its keys at one revision.
// Violated: each cached Get answers at its own entry's revision (txn.go: evalOps), with only the
// latest header for the whole (TestLeasingTxnAtomicCache checks ModRevisions only).
func UnmetTxnAtomicCache(ctx context.Context, lkv clientv3.KV, k1, k2 string) {
	t, err := lkv.Txn(ctx).Then(clientv3.OpGet(k1), clientv3.OpGet(k2)).Commit()
	if err != nil || len(t.Responses) != 2 {
		return
	}
	r1, r2 := t.Responses[0].GetResponseRange(), t.Responses[1].GetResponseRange()
	if r1.Header != nil && r2.Header != nil && r1.Header.Revision != r2.Header.Revision {
		panic("txn-atomic-cache: ranges at different revisions")
	}
}
