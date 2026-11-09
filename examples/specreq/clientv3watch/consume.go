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

// REQ clientv3watch/prev-kv-compacting: under compaction, an update's PrevKv is either nil (the
// caller treats it as an error) or the key's previous value.
// Users: Kubernetes' etcd3 watcher (event.go:67: a non-create event with a nil PrevKv is an error).
// Assumes: k is owned (compaction allowed).
// Specs: Client.Put.spec, Client.Watch.spec, WithPrevKV.spec; watchStep (WatchReq.prevOk).
func ReqWatchPrevKVCompacting(ctx context.Context, cli *clientv3.Client, k string) {
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
			if ev.PrevKv == nil {
				return // Kubernetes: an error, the watch restarts
			}
			if string(ev.PrevKv.Value) != "v1" {
				panic("prev-kv-compacting: a non-nil PrevKv is the previous value")
			}
			return
		}
	}
}

// REQ clientv3watch/share: a received response's events may be read by several goroutines (made
// read-only), as the cache hands one response's events to every watcher and keeps them.
// Users: the cache (demux.go:218,227,281), Election.observe (forwards one header, election.go:238).
// Assumes: none.
// Specs: Client.Watch.spec; watchRespAt_persist, watchRespRO_persistent, eventOwn_unfold.
func ReqWatchShare(ctx context.Context, cli *clientv3.Client, pfx string) {
	for wr := range cli.Watch(ctx, pfx, clientv3.WithPrefix()) {
		evs := wr.Events
		done := make(chan struct{})
		go func() {
			for _, ev := range evs {
				_ = len(ev.Kv.Key)
			}
			close(done)
		}()
		for _, ev := range evs {
			_ = len(ev.Kv.Value)
		}
		_ = wr.Header.Revision
		<-done
	}
}

// REQ clientv3watch/options: the watch options and contexts its users pass never make Watch
// panic: a require-leader context (every Kubernetes watch), a range (authkv, the namespace
// wrapper), the empty key with a prefix (every key), the buffer-wait logging (Kubernetes).
// Users: Kubernetes' etcd3 watcher (watcher.go:489-493), examples/etcd/auth/authkv.go:434,445,
// namespace/watch.go:49, grpcproxy/leader.go:62.
// Assumes: none.
// Specs: WithRequireLeader.spec (ctxOk, ctxPrin kept), Client.Watch.spec, WithRange.spec,
// WithPrefix.spec, WithWatchBufLog.spec, WithRev.spec.
func ReqWatchOptions(ctx context.Context, cli *clientv3.Client, a, b string) {
	lctx := clientv3.WithRequireLeader(ctx)
	_ = cli.Watch(lctx, "", clientv3.WithPrefix(), clientv3.WithRev(1))
	_ = cli.Watch(lctx, a, clientv3.WithRange(b), clientv3.WithWatchBufLog())
}
