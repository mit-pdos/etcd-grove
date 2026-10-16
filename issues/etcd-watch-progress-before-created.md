---
upstream: unchecked
---

# A progress notification can reach a watch created after it, before the watch's events

- **Fix** (the user's decision, 2026-10-16: folded into the verified fork): fork commit `c267e0ffe`
  (branch `watch-progress-before-created`, on upstream `f061acd09`; not pushed), cherry-picked onto
  `goose-lean` as `09669450f` (not pushed): before sending a `Created` response, `sendLoop` sends
  the watch responses already queued on the watch channel (a non-blocking receive until the
  channel is empty; the handling of a watch response moved into a closure `sendWatch`, used by
  both cases). With it the reproduction finds no hit in 3 × 500 trials (without: a hit within 47,
  252, 373 trials); v3rpc's unit tests and `tests/integration/clientv3/watch` pass. The commit
  adds the reproduction as `TestWatchProgressBeforeCreatedRace`. A bounded drain
  (`len(sws.watchStream.Chan())` responses) was the first version; it passes the same tests, but
  Perennial's `Len` spec (`wp_Len`) only bounds the result, so the proof could not use it.
- **Status**: bug (a wrong result): a watch created from an old revision can receive, as its first
  response, a progress notification at a revision above events it has not received yet. A client
  that reads a progress notification as "nothing changed under my range up to this revision" (its
  documented meaning; etcd's `cache` package does) then skips those events or sees them go
  backwards.
- **Where** (`upamanyus/etcd` `goose-lean` `107edf7e4`, the same code as upstream `main`
  `f061acd09`):
  - `server/etcdserver/api/v3rpc/watch.go`: `recvLoop` (249) handles a progress request by
    `sws.watchStream.RequestProgressAll()` (398), which puts the `-1` response on the mvcc stream's
    channel at once (`watchableStore.progressIfSync`, `server/storage/mvcc/watchable_store.go`
    517–543: when every watcher of the stream is synced, at the store's current revision); a later
    create request registers the watcher (`sws.watchStream.Watch`, 340) and puts its `Created`
    response on `sws.ctrlStream` (367);
  - `sendLoop` (411) selects between the mvcc channel (435) and `ctrlStream` (514), so with both
    ready it can send the `Created` response before the progress response that was queued first;
  - `client/v3/watch.go`: `run` moves the new substream into `substreams` on `Created`, and then
    broadcasts the progress response (watch id `-1`) to every substream (`broadcastResponse`, 745),
    the new one included.
- **What happens**: on one gRPC watch stream, the client sends a progress request and then a create
  request for a watch from an old revision (`WithRev(2)`). The server answers the progress request
  when the stream's watchers are synced, at revision `r`; the new watcher is registered after, and
  unsynced (its events from revision 2 are still to be sent). If `sendLoop` sends `Created` first,
  the client broadcasts the progress notification at `r` to the new watch before any of its events.

  Reproduction: `tests/integration/clientv3/watch/zz_progress_created_race_test.go` (below), run
  from `tests/` with `go test ./integration/clientv3/watch -run TestWatchProgressBeforeCreatedRace
  -count=1 -v` on a checkout of upstream `main` (`f061acd09`; checked on the fork's
  `watch-progress-closed-substream` branch, whose one commit changes only the client's handling of
  canceled substreams). Three runs, each a hit, after 47, 252 and 373 trials (`progress
  notification at revision 1393 before the watch's events (from revision 2)`).

  ```go
package watch

import (
	"context"
	"sync"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestWatchProgressBeforeCreatedRace(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)
	ctx := t.Context()
	for i := 0; i < 10; i++ {
		if _, err := cli.Put(ctx, "k", "v"); err != nil {
			t.Fatal(err)
		}
	}
	hits, trials := 0, 0
	for trial := 0; trial < 500 && hits == 0; trial++ {
		trials++
		tctx, cancel := context.WithCancel(ctx)
		bw := cli.Watch(tctx, "busy", clientv3.WithPrefix())
		var wg sync.WaitGroup
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 30; j++ {
				cli.Put(ctx, "busy/x", "v")
			}
		}()
		time.Sleep(time.Millisecond)
		if err := cli.RequestProgress(tctx); err != nil {
			t.Fatal(err)
		}
		wch := cli.Watch(tctx, "k", clientv3.WithRev(2), clientv3.WithProgressNotify())
		select {
		case resp := <-wch:
			if resp.IsProgressNotify() {
				hits++
				t.Logf("trial %d: progress notification at revision %d before the watch's events (from revision 2)",
					trial, resp.Header.Revision)
			}
		case <-time.After(5 * time.Second):
			t.Fatal("no response on the new watch")
		}
		cancel()
		for range bw {
		}
		wg.Wait()
	}
	if hits > 0 {
		t.Fatalf("%d of %d trials: a progress notification reached a new watch before its events", hits, trials)
	}
	t.Logf("no hit in %d trials", trials)
}
  ```

  A progress notification before the watch's events can only come from the broadcast: a
  per-watcher progress notification (`RequestProgress` of the server's watch stream, the periodic
  `WithProgressNotify` one) is sent only for a synced watcher, and the new watcher is unsynced.
- **Expected**: a progress notification at revision `r` on a watch means the watch has received
  every event of its range up to `r` (the `WithProgressNotify` and `RequestProgress`
  documentation: "the client ... has seen all events up to that revision"); a watch created after
  the server answered the progress request should not receive it.
- **How the proof handles it**: found while designing the watch slice's unit W-K (the cache over
  etcd's client watcher, `notes/STATUS.md`, "W-K"): mvcc's progress response is specified to cover
  the watchers of the stream's map when it is sent, which does not include a watcher registered
  after it; the client's contract for a broadcast progress response cannot hold for such a watch.
  The proof is being decided (a fix in the verified fork, or a contract without broadcast
  coverage).
- **Possible fixes**: in `sendLoop`, keep the order between a progress response and later control
  responses (e.g. answer `RequestProgressAll` on `ctrlStream`, or have `recvLoop` wait until the
  progress response is sent before handling the next request); or in the client, broadcast a
  progress response only to the substreams created before the progress request was sent.
- **Found**: 2026-10-16, the watch slice's unit W-K (designing the progress responses' contract).
