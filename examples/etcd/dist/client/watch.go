package client

import (
	"context"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/cache/v3"
	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// readTimeout bounds how long a workload reads its watch after its writers are done, so that a
// client machine's program ends (a liveness bound, not a check: the watch's context is cancelled,
// its channel closes, and the read reports an end without a check).
const readTimeout = 2 * time.Minute

// RunWatch is the watch workload (partition.MainWatch minus its start and partitioner, copied:
// MainWatch is one function with its start; Lean: Workload.watch): the writers' Puts picked (nops
// each) under watchPrefix; a watch of the prefix from revision 1, opened before any write through
// a client of its own (the watcher), kept across faults (the client re-opens its stream at a
// reachable member and resumes it); the writers, each at its own machine (nodes[c]: remoteWriters,
// NodeMain) through its own client; then the watch read
// until it has reported every successful Put (etcdstart.Collect: a closed channel or an error
// response is an end, never "complete") and checked against the writes (etcdstart.Check: exactly
// the writes, gap-free from revision 2, so the deployment's only workload writing keys).
func RunWatch(eps []string, nodes []string, nops int, ready func()) Result {
	tried := etcdstart.GenAll(len(nodes)*nops, []string{watchPrefix + "k0", watchPrefix + "k1", watchPrefix + "k2"})
	watcher, err := newClient(eps)
	if err != nil {
		return ended("watch: the watcher failed to connect")
	}
	if !AwaitAccept(nodes) {
		return ended("watch: a writer's machine never answered")
	}
	wctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	wch := watcher.Watcher.Watch(wctx, watchPrefix, clientv3.WithPrefix(), clientv3.WithRev(1),
		clientv3.WithProgressNotify(), clientv3.WithCreatedNotify())
	ready()
	oks := remoteWriters(nodes, tried, nops)
	t := time.AfterFunc(readTimeout, cancel)
	evs, ok := etcdstart.Collect(wch, etcdstart.MaxRev(oks))
	t.Stop()
	cancel()
	if !ok {
		return ended("watch: the watch ended before it reported every successful Put")
	}
	etcdstart.Check("dist watch", "put", evs, tried, oks)
	return checked()
}

// RunCache is the cache workload (cache.Main minus its start, copied with its unexported helpers
// cacheCollect, awaitProgress, checkProgress, lastVal, hasKey, checkGet; Lean: Workload.cache):
// etcd's watch cache of cachePrefix over a client of its own, a cache watch of the prefix from
// revision 2 opened before any write, len(nodes) writers of nops Puts each, at their own machines
// through their own clients (remoteWriters);
// then the watch read until it has reported every successful Put and checked as the watch
// workload's; a progress notification requested and awaited, whose revision must be at most the
// last event's; and the cache's Get of the prefix at the highest successful Put's revision, which
// must answer each key's last watched value at or below it. The deployment's only workload writing
// keys.
func RunCache(eps []string, nodes []string, nops int, ready func()) Result {
	tried := etcdstart.GenAll(len(nodes)*nops, []string{cachePrefix + "k0", cachePrefix + "k1", cachePrefix + "k2"})
	ccli, err := newClient(eps)
	if err != nil {
		return ended("cache: the cache's client failed to connect")
	}
	if !AwaitAccept(nodes) {
		return ended("cache: a writer's machine never answered")
	}
	c, err := cache.New(ccli, cachePrefix)
	if err != nil {
		return ended("cache: cache.New failed")
	}
	defer c.Close()
	wctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	wch := c.Watch(wctx, cachePrefix, clientv3.WithPrefix(), clientv3.WithRev(2))
	ready()
	oks := remoteWriters(nodes, tried, nops)
	t := time.AfterFunc(readTimeout, cancel)
	defer t.Stop()
	r := etcdstart.MaxRev(oks)
	evs, ok := cacheCollect(wch, r)
	if !ok {
		return ended("cache: the watch ended before it reported every successful Put")
	}
	c.RequestProgress(wctx)
	p, evs, ok := awaitProgress(wch, evs)
	cancel()
	if !ok {
		return ended("cache: the watch ended before a progress notification")
	}
	checkProgress(evs, p)
	etcdstart.Check("dist cache", "Put", evs, tried, oks)
	if r != 0 {
		gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		gresp, err := c.Get(gctx, cachePrefix, clientv3.WithPrefix(), clientv3.WithRev(r))
		gcancel()
		if err != nil {
			return ended("cache: the cache's Get failed")
		}
		checkGet(evs, r, gresp.Kvs)
	}
	return checked()
}

// cacheCollect is cache's collect (copied): it reads the cache's watch channel wch until an event
// at revision upTo or above (at once if upTo is 0), returning the events read and true; false if
// the channel closed, or a response was a cancel or a compaction's, before.
func cacheCollect(wch clientv3.WatchChan, upTo int64) ([]etcdstart.Event, bool) {
	var evs []etcdstart.Event
	var last int64
	if upTo == 0 {
		return evs, true
	}
	for wresp := range wch {
		if wresp.Canceled || wresp.CompactRevision != 0 {
			return evs, false
		}
		for _, e := range wresp.Events {
			evs = append(evs, etcdstart.Event{Rev: e.Kv.ModRevision, Key: string(e.Kv.Key),
				Val: string(e.Kv.Value), Put: e.Type == mvccpb.Event_PUT})
			last = e.Kv.ModRevision
		}
		if len(evs) > 0 && last >= upTo {
			return evs, true
		}
	}
	return evs, false
}

// awaitProgress (cache's, copied) reads wch until a progress notification, appending the events of
// the responses before it to evs: the notification's revision, the events, and whether it came
// before the channel closed or a response was a cancel or a compaction's.
func awaitProgress(wch clientv3.WatchChan, evs []etcdstart.Event) (int64, []etcdstart.Event, bool) {
	for wresp := range wch {
		if wresp.Canceled || wresp.CompactRevision != 0 {
			return 0, evs, false
		}
		if wresp.IsProgressNotify() {
			return wresp.Header.Revision, evs, true
		}
		for _, e := range wresp.Events {
			evs = append(evs, etcdstart.Event{Rev: e.Kv.ModRevision, Key: string(e.Kv.Key),
				Val: string(e.Kv.Value), Put: e.Type == mvccpb.Event_PUT})
		}
	}
	return 0, evs, false
}

// checkProgress (cache's, copied) panics unless the progress notification's revision p is at most
// the last watched event's revision (1 if none): with a put under the prefix at every revision from
// 2 on, a notification above it would claim the watch complete past an event it did not send.
func checkProgress(evs []etcdstart.Event, p int64) {
	last := int64(1)
	if len(evs) > 0 {
		last = evs[len(evs)-1].Rev
	}
	if p > last {
		panic("dist cache: a progress notification above an event the watch did not send")
	}
}

// lastVal (cache's, copied) is the value of the last of the events evs of key at or below r.
func lastVal(evs []etcdstart.Event, key string, r int64) (string, bool) {
	v, ok := "", false
	for _, e := range evs {
		if e.Rev <= r && e.Key == key {
			v, ok = e.Val, true
		}
	}
	return v, ok
}

// hasKey (cache's, copied) reports whether one of kvs has the key key.
func hasKey(kvs []*mvccpb.KeyValue, key string) bool {
	for _, kv := range kvs {
		if string(kv.Key) == key {
			return true
		}
	}
	return false
}

// checkGet (cache's, copied) panics unless kvs, a Get of the prefix at revision r, are exactly the
// last values of the watch's events evs at or below r.
func checkGet(evs []etcdstart.Event, r int64, kvs []*mvccpb.KeyValue) {
	for _, kv := range kvs {
		v, ok := lastVal(evs, string(kv.Key), r)
		if !ok || v != string(kv.Value) {
			panic("dist cache: the cache's Get disagrees with the watch")
		}
	}
	for _, e := range evs {
		if e.Rev <= r && !hasKey(kvs, e.Key) {
			panic("dist cache: the cache's Get misses a watched key")
		}
	}
}
