// Package cache holds the requirement snippets of etcd's cache (go.etcd.io/etcd/cache/v3; batch 1g,
// SpecPlan/Spec/go_etcd_io/etcd/cache/v3/): minimal uses of the patterns its users rely on
// (examples/etcd/cache/cachekv.go, etcd's tests/integration/cache_test.go), each reliance an
// explicit panic.
//
// Common assumptions (the proofs' setting): cli is a client of a cluster (isClient), the caller owns
// the cluster's state etcdState in an invariant of its own (it gives New the read permission
// etcdPeek and takes etcdLb anchors from it), keys under the snippet's prefix are written only by
// the snippet (an invariant clause) and attached to no lease; contexts are contexts with no
// metadata (ctxPrin of the client's principal); the cluster's history meets the compaction
// condition (EtcdModel.exactFrom σ.kv 0 at every state it reaches: no transaction puts and deletes
// one key, or no compaction; an invariant clause), under which the cache's contents and its
// watches' events and progress notifications are exact (they come from its upstream client watch).
package cache

import (
	"context"
	"errors"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/cache/v3"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ cache/get-after-put: a linearizable cache Get after an acknowledged Put sees it (or a later
// write), at a header revision at least the Put's.
// Users: tests/integration/cache_test.go testWithPrefixGet, testGet (the cache as a Getter in
// place of the client).
// Assumes: k is under the cache's prefix and written only here.
// Specs: Client.Put.spec (KV.PutTriple), Cache.Get.spec (getOk: σ0 the Put's state, etcdLb_ord).
func ReqGetAfterPut(ctx context.Context, cli *clientv3.Client, c *cache.Cache, k, v string) {
	presp, err := cli.Put(ctx, k, v)
	if err != nil {
		return
	}
	gresp, err := c.Get(ctx, k)
	if err != nil {
		return
	}
	if gresp.Header.Revision < presp.Header.Revision {
		panic("get-after-put: stale header")
	}
	if len(gresp.Kvs) != 1 || string(gresp.Kvs[0].Value) != v {
		panic("get-after-put: lost write")
	}
}

// lastPut is cachekv's lastVal: the value of the last put event of key at or below r.
func lastPut(evs []*mvccpb.Event, key string, r int64) (string, bool) {
	v, ok := "", false
	for _, e := range evs {
		if e.Kv.ModRevision <= r && string(e.Kv.Key) == key {
			v, ok = string(e.Kv.Value), e.Type == mvccpb.PUT
		}
	}
	return v, ok
}

// REQ cache/get-agrees-with-watch: a Get at a revision r agrees, key by key, with a watch's events
// read gap-free from a revision below every write up to r.
// Users: examples/etcd/cache/cachekv.go (checkGet).
// Assumes: evs are the events a cache watch of pfx from revision 2 delivered, up to and including
// revision r (ReqWatchFromRev's loop); every key under pfx was written after revision 1.
// Specs: Cache.Watch.spec, cacheWatchAt_recv (deliv), Cache.Get.spec (getOk at rev = r);
// laws: etcdLb_ord (both are the one history).
func ReqGetAgreesWithWatch(ctx context.Context, c *cache.Cache, pfx string, evs []*mvccpb.Event, r int64) {
	gresp, err := c.Get(ctx, pfx, clientv3.WithPrefix(), clientv3.WithRev(r))
	if err != nil {
		return
	}
	for _, kv := range gresp.Kvs {
		if v, ok := lastPut(evs, string(kv.Key), r); !ok || v != string(kv.Value) {
			panic("get-agrees-with-watch: a value the watch did not report")
		}
	}
	for _, e := range evs {
		if _, ok := lastPut(evs, string(e.Kv.Key), r); ok {
			found := false
			for _, kv := range gresp.Kvs {
				if string(kv.Key) == string(e.Kv.Key) {
					found = true
				}
			}
			if !found {
				panic("get-agrees-with-watch: a watched key missing")
			}
		}
	}
}

// REQ cache/wait-then-serializable: after WaitForRevision(rev) returns nil, a serializable Get
// answers at a header revision at least rev.
// Users: tests/integration/cache_test.go testGet (WaitForRevision, then Gets).
// Assumes: nothing.
// Specs: Cache.WaitForRevision.spec (cacheRevLb), Cache.Get.spec (r0).
func ReqWaitThenSerializable(ctx context.Context, c *cache.Cache, k string, rev int64) {
	if err := c.WaitForRevision(ctx, rev); err != nil {
		return
	}
	gresp, err := c.Get(ctx, k, clientv3.WithSerializable())
	if err != nil {
		return
	}
	if gresp.Header.Revision < rev {
		panic("wait-then-serializable: the cache went back")
	}
}

// REQ cache/range-invalid: a Get outside a prefix cache's prefix fails with ErrKeyRangeInvalid
// (the context alive); an unsupported option fails.
// Users: tests/integration/cache_test.go TestCacheWithPrefixGetOutOfScope,
// TestCacheUnsupportedGetOptions.
// Assumes: c is a cache of "/foo"; ctx is not done (the caller's own context).
// Specs: Cache.Get.spec (getErr), init.spec; laws: wrapsErr_refl, errorsIs_wraps.
func ReqRangeInvalid(ctx context.Context, c *cache.Cache) {
	if _, err := c.Get(ctx, "/bar/a", clientv3.WithSerializable()); err == nil {
		panic("range-invalid: served a key outside the prefix")
	} else if ctx.Err() == nil && !errors.Is(err, cache.ErrKeyRangeInvalid) {
		panic("range-invalid: wrong error")
	}
	if _, err := c.Get(ctx, "/foo/a", clientv3.WithCountOnly()); err == nil {
		panic("range-invalid: served an unsupported option")
	} else if ctx.Err() == nil && !errors.Is(err, cache.ErrUnsupportedRequest) {
		panic("range-invalid: an unsupported option's error is not ErrUnsupportedRequest")
	}
}

// REQ cache/get-future-rev: a serializable Get at a revision the cluster has not reached fails
// with ErrFutureRev (the context alive).
// Users: tests/integration/cache_test.go testGet (12 cases: errors.Is(err, rpctypes.ErrFutureRev),
// serializable and not; the linearizable ones also pass when the client's own Get succeeds).
// Assumes: the cluster's revision is r and nobody writes during the call (the owner's invariant);
// k is in the cache's range; ctx is not done (the caller's own context).
// Specs: Cache.Get.spec (getErr's ErrFutureRev clause, getOk's o.rev <= L <= σ.kv.rev);
// laws: etcdLb_reach, errorsIs_errVal.
func ReqGetFutureRev(ctx context.Context, c *cache.Cache, k string, r int64) {
	_, err := c.Get(ctx, k, clientv3.WithSerializable(), clientv3.WithRev(r+1))
	if err == nil {
		panic("get-future-rev: answered at a revision the cluster has not reached")
	}
	if ctx.Err() == nil && !errors.Is(err, rpctypes.ErrFutureRev) {
		panic("get-future-rev: wrong error")
	}
}
