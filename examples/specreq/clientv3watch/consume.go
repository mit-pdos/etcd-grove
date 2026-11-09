package clientv3watch

import (
	"bytes"
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3watch/select: a watch channel read in a select with the context, as the
// order requirement (events after the position, in order).
// Users: Kubernetes' etcd3 watcher, the cache (cache.go: select on internalCtx.Done, the watch
// channel and applyErr), naming/endpoints (select on ctx.Done), grpcproxy's health check.
// Assumes: none.
// Specs: Client.Watch.spec; watchChAt_recvAu (the receive as a select case), Context.ctxOk's Done.
func ReqWatchSelect(ctx context.Context, cli *clientv3.Client, k string, rev int64) {
	if rev <= 0 {
		return
	}
	wch := cli.Watch(ctx, k, clientv3.WithRev(rev))
	last := rev - 1
	for {
		select {
		case <-ctx.Done():
			return
		case wr, ok := <-wch:
			if !ok || wr.Err() != nil {
				return
			}
			prev := last
			for _, ev := range wr.Events {
				if ev.Kv.ModRevision <= prev || ev.Kv.ModRevision < last {
					panic("select: an event before the start, repeated or out of order")
				}
				last = ev.Kv.ModRevision
			}
		}
	}
}

// REQ clientv3watch/rewrite: a watch's response belongs to its consumer: it may rewrite an
// event's key and the header's revision; every event's key is in the watched range.
// Users: concurrency's Election.Observe (election.go:190: wr.Header.Revision = kv.ModRevision),
// the namespace wrapper (namespace/watch.go: ev.Kv.Key = ev.Kv.Key[len(pfx):], relying on the
// prefix: a shorter key would panic on the slice).
// Assumes: none.
// Specs: Client.Watch.spec, WithPrefix.spec; watchRespAt_fields (the header owned in full with
// events, the events in full), eventOwn_unfold, keyValueOwn_unfold; watchStep (WatchReq.keeps:
// the key in the range).
func ReqWatchRewrite(ctx context.Context, cli *clientv3.Client, pfx string) {
	for wr := range cli.Watch(ctx, pfx, clientv3.WithPrefix()) {
		if wr.Err() != nil {
			return
		}
		for _, ev := range wr.Events {
			if !bytes.HasPrefix(ev.Kv.Key, []byte(pfx)) {
				panic("rewrite: an event outside the watched prefix")
			}
			ev.Kv.Key = ev.Kv.Key[len(pfx):]
			if ev.PrevKv != nil {
				ev.PrevKv.Key = ev.Kv.Key
			}
			wr.Header.Revision = ev.Kv.ModRevision
		}
	}
}

// REQ clientv3watch/prev-kv: with WithPrevKV, an update's event carries the key's previous
// value (when nothing compacted the revision before it).
// Users: Kubernetes' etcd3 watcher (event.go:67: a non-create event without PrevKv is an error;
// the old object is PrevKv's value), grpcproxy (forwards PrevKv).
// Assumes: k is owned; the cluster never compacts (no Compact call, no auto-compactor:
// envUpd's cfg.autoCompact = false), so its compaction revision stays 0.
// Specs: Client.Put.spec, Client.Watch.spec, WithPrevKV.spec, WithRev.spec; watchStep
// (WatchReq.prevOk).
func ReqWatchPrevKV(ctx context.Context, cli *clientv3.Client, k string) {
	if _, err := cli.Put(ctx, k, "v1"); err != nil {
		return
	}
	p, err := cli.Put(ctx, k, "v2")
	if err != nil {
		return
	}
	for wr := range cli.Watch(ctx, k, clientv3.WithRev(p.Header.Revision), clientv3.WithPrevKV()) {
		if wr.Err() != nil {
			return
		}
		for _, ev := range wr.Events {
			if ev.PrevKv == nil || string(ev.PrevKv.Value) != "v1" || string(ev.Kv.Value) != "v2" {
				panic("prev-kv: the update's previous value")
			}
			return
		}
	}
}
