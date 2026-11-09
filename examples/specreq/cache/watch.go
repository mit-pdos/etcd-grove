package cache

import (
	"context"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/cache/v3"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ cache/watch-from-rev: a cache watch from revision 2 reports the writes under its range in
// revision order, gap-free: an acknowledged Put at revision r appears as the event at r, and no
// event is reported twice.
// Users: examples/etcd/cache/cachekv.go (collect, etcdstart.Check).
// Assumes: k is under the cache's prefix and written only here, after revision 1; the owner's
// invariant records the Put's state (etcdLb) so its event is in the history at its revision.
// Specs: Cache.Watch.spec (watchStart: live (some 2)), cacheWatchAt_recv (deliv: evsBetween),
// Client.Put.spec.
func ReqWatchFromRev(ctx context.Context, cli *clientv3.Client, c *cache.Cache, k, v string) {
	wch := c.Watch(ctx, k, clientv3.WithRev(2))
	presp, err := cli.Put(ctx, k, v)
	if err != nil {
		return
	}
	last := int64(1)
	for wresp := range wch {
		if wresp.Canceled {
			return
		}
		var es []*mvccpb.Event = wresp.Events
		for _, e := range es {
			if e.Kv.ModRevision <= last {
				panic("watch-from-rev: an event out of order or repeated")
			}
			last = e.Kv.ModRevision
			if last == presp.Header.Revision {
				if e.Type != mvccpb.PUT || string(e.Kv.Value) != v {
					panic("watch-from-rev: the write's event is wrong")
				}
				return
			}
			if last > presp.Header.Revision {
				panic("watch-from-rev: the write's revision skipped")
			}
		}
	}
}

// REQ cache/progress-quiet: a progress notification at p says the watch reported every event
// under its range up to p: with a write at every revision from 2 on (each under the range), p is
// at most the last event's revision.
// Users: examples/etcd/cache/cachekv.go (awaitProgress, checkProgress); tests/integration
// TestCacheRequestProgress, TestCacheProgressNotify.
// Assumes: every revision from 2 on has an event under k's prefix (the caller's workload); the
// watch was opened from revision 2.
// Specs: Cache.RequestProgress.spec, cacheWatchAt_recv (quiet).
func ReqProgressQuiet(ctx context.Context, c *cache.Cache, pfx string) {
	wch := c.Watch(ctx, pfx, clientv3.WithPrefix(), clientv3.WithRev(2))
	c.RequestProgress(ctx)
	last := int64(1)
	for wresp := range wch {
		if wresp.Canceled || wresp.CompactRevision != 0 {
			return
		}
		if wresp.IsProgressNotify() {
			if wresp.Header.Revision > last {
				panic("progress-quiet: a notification past an unreported event")
			}
			return
		}
		var es []*mvccpb.Event = wresp.Events
		for _, e := range es {
			last = e.Kv.ModRevision
		}
	}
}

// REQ cache/watch-ends: a watch's channel may close (context done, cache closed, upstream restart)
// or end with a compaction's cancel; nothing comes after either. A consumer that stops reading
// on either never panics; receiving again from a closed channel gets nothing.
// Users: examples/etcd/cache/cachekv.go (WatchEnded), tests/integration TestCacheLaggingWatcher.
// Assumes: nothing.
// Specs: Cache.Watch.spec, Cache.WaitForNextResync.spec, cacheWatchAt_recv (closed, cancel).
func ReqWatchEnds(ctx context.Context, c *cache.Cache, pfx string) {
	wch := c.Watch(ctx, pfx, clientv3.WithPrefix())
	if err := c.WaitForNextResync(ctx); err != nil {
		return
	}
	for wresp := range wch {
		if wresp.Canceled {
			if _, ok := <-wch; ok {
				panic("watch-ends: a response after the cancel")
			}
			return
		}
	}
	if _, ok := <-wch; ok {
		panic("watch-ends: a response after the close")
	}
}

// REQ cache/watch-rejected: a request the cache does not serve gets one cancel response, then the
// channel closes.
// Users: tests/integration TestCacheWatchUnsupportedOptions, TestCacheWithPrefixWatchOutOfScope.
// Assumes: c is ready (else the channel may close at once, which the snippet also accepts).
// Specs: Cache.Watch.spec (watchStart: rejected), cacheWatchAt_recv (rejected).
func ReqWatchRejected(ctx context.Context, c *cache.Cache, pfx string) {
	wch := c.Watch(ctx, pfx, clientv3.WithPrefix(), clientv3.WithPrevKV())
	wresp, ok := <-wch
	if !ok {
		return
	}
	if !wresp.Canceled || len(wresp.Events) != 0 {
		panic("watch-rejected: served an unsupported request")
	}
	if _, ok := <-wch; ok {
		panic("watch-rejected: more than one response")
	}
}
