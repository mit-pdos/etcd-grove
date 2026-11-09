package clientv3watch

import (
	"context"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3watch/compacted: a compaction ends the watch with ErrCompacted and a compaction
// revision past the watch's start: the revisions it still needed are gone.
// Users: every watch user (Kubernetes' watcher reports "too old resource version", the cache
// relists, concurrency's waitDelete returns the error); examples/etcd/compactwatch/compactkv.go:142
// (etcdstart.CompactRev reads CompactRevision).
// Assumes: none.
// Specs: Client.Watch.spec, WithRev.spec, WatchResponse.Err.spec; watchStep's error case
// (cr ≤ compacted, last event's revision (or start - 1) + 1 < cr; not a progress's), closeErrOk.
func ReqWatchCompacted(ctx context.Context, cli *clientv3.Client, k string, rev int64) {
	if rev <= 0 {
		return
	}
	for wr := range cli.Watch(ctx, k, clientv3.WithRev(rev)) {
		if wr.CompactRevision != 0 {
			if wr.Err() != rpctypes.ErrCompacted || !wr.Canceled {
				panic("compacted: ErrCompacted, canceled")
			}
			if wr.CompactRevision <= rev {
				panic("compacted: a compaction revision at or below the start")
			}
			return
		}
	}
}

// REQ clientv3watch/ends: after an error response, a watch delivers no event (only further error
// responses, then the channel closes).
// Users: the recipes (watch.go: return on the first error), Kubernetes' watcher (an error ends
// its watch), concurrency's Election.Observe (election.go:223: does not check Err, relies on an
// error response having no events).
// Assumes: none.
// Specs: Client.Watch.spec; watchStep (an ended position: errors only).
func ReqWatchEnds(ctx context.Context, cli *clientv3.Client, k string) {
	ended := false
	for wr := range cli.Watch(ctx, k, clientv3.WithPrefix()) {
		if ended && (len(wr.Events) > 0 || wr.Err() == nil) {
			panic("ends: a response after the error")
		}
		if wr.Err() != nil {
			if len(wr.Events) > 0 {
				panic("ends: an error with events")
			}
			ended = true
		}
	}
}

// REQ clientv3watch/created-first: with WithCreatedNotify, a Created response can only be the
// first one received.
// Users: grpcproxy's leader probe (leader.go:62: the first response is the creation, any later
// one is a loss), its health check (health.go:73), the cache (its first response marks it ready).
// Assumes: none.
// Specs: Client.Watch.spec, WithCreatedNotify.spec; watchStep (Created only when not started).
func ReqWatchCreatedFirst(ctx context.Context, cli *clientv3.Client, k string) {
	first := true
	for wr := range cli.Watch(ctx, k, clientv3.WithCreatedNotify()) {
		if wr.Created && !first {
			panic("created-first: a Created response after another")
		}
		first = false
	}
}

// (No snippet for a refused watch: examples/etcd/auth/authkv.go:272 panics on any event of a
// watch its user may not read, which holds of an up-to-date member only: a lagging member admits a
// watch at its applied auth state, any state the cluster reached, auth off at the start included.
// The spec states that (watchStep's σa); the example's check rests on its single member. An open
// question of batch 1b.)

// REQ clientv3watch/close: closing a watcher, twice, and watching after it never panics.
// Users: Client.Close (client.go:150), the namespace wrapper (namespace/watch.go:79).
// Assumes: none.
// Specs: NewWatcher.spec (via the client's connection, isClient_conn), watcher.Close.spec,
// watcher.Watch.spec (Watcher.CloseTriple, Watcher.WatchTriple).
func ReqWatcherClose(ctx context.Context, cli *clientv3.Client, k string) {
	w := clientv3.NewWatcher(cli)
	_ = w.Close()
	_ = w.Close()
	_ = w.Watch(ctx, k)
}
