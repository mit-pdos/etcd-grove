package clientv3watch

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3watch/progress-complete: a progress notification at P means every event of the
// range up to P has been delivered: one at or past an acknowledged write that was not delivered
// would be a lie.
// Users: Kubernetes' etcd3 watcher (progress bookmarks raise the watch cache's resource version),
// the cache (a progress response sets maxRev; waitTillRevision serves reads up to it), the
// examples' awaitProgress (examples/etcd/cache/cachekv.go: panics if the progress revision passes
// the last event).
// Assumes: pfx is owned.
// Specs: Client.Get.spec, Client.Put.spec, Client.Watch.spec, WithProgressNotify.spec,
// WatchResponse.IsProgressNotify.spec; watchStep's progress case (no event of the watch between
// the position and P).
func ReqWatchProgressComplete(ctx context.Context, cli *clientv3.Client, pfx string) {
	g, err := cli.Get(ctx, pfx, clientv3.WithPrefix())
	if err != nil {
		return
	}
	p, err := cli.Put(ctx, pfx+"a", "1")
	if err != nil {
		return
	}
	for wr := range cli.Watch(ctx, pfx, clientv3.WithPrefix(), clientv3.WithRev(g.Header.Revision+1),
		clientv3.WithProgressNotify()) {
		if wr.Err() != nil {
			return
		}
		if wr.IsProgressNotify() && wr.Header.Revision >= p.Header.Revision {
			panic("progress-complete: a progress past an undelivered write")
		}
		if len(wr.Events) > 0 {
			return
		}
	}
}

// REQ clientv3watch/request-progress: asking for progress on a context's stream never panics,
// whatever the context and whether or not a watch uses it; the error is only logged.
// Users: the cache (progress_requestor.go:94), Kubernetes (etcd3/store.go:108, watcher.go:303).
// Assumes: none.
// Specs: Client.RequestProgress.spec (Watcher.RequestProgressTriple).
func ReqRequestProgress(ctx context.Context, cli *clientv3.Client) {
	if err := cli.RequestProgress(ctx); err != nil {
		return
	}
}
