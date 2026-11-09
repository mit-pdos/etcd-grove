package recipes

import (
	"context"

	"go.etcd.io/etcd/api/v3/mvccpb"
	recipe "go.etcd.io/etcd/client/v3/experimental/recipes"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ recipes/wait-first-delete: WaitEvents from a revision returns the first event of the
// requested type at or after it, with the key and the revision it happened at.
// Users: Barrier.Wait, DoubleBarrier.Enter/Leave, RWMutex.waitOnLastRev (in the package);
// T/v3_closed_watch_test.go:102-119 (a compacted start revision: an error, never a nil event).
// Assumes: k owned.
// Specs: WaitEvents.spec (es ++ [e] a prefix of watchHist from rev, matchCount: e the first
// delete), watchEvOwn_unfold, Client.Put.spec, Client.Delete.spec.
func ReqWaitFirstDelete(ctx context.Context, c *clientv3.Client, k string) {
	p, err := c.Put(ctx, k, "v")
	if err != nil {
		return
	}
	d, err := c.Delete(ctx, k)
	if err != nil {
		return
	}
	ev, err := recipe.WaitEvents(c, k, p.Header.Revision, []mvccpb.Event_EventType{mvccpb.Event_DELETE})
	if err != nil {
		return
	}
	if ev == nil || ev.Type != mvccpb.Event_DELETE || string(ev.Kv.Key) != k ||
		ev.Kv.ModRevision != d.Header.Revision {
		panic("wait-first-delete: not the first delete after the revision")
	}
}
