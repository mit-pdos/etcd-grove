# The watch client's progress broadcast can send on a canceled substream's closed `recvc`

- **Status**: open (not reported).
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `bc8b52a50` (the same code as upstream
  `main`; the pinned `457b8d1b6` adds one line at 868, shifting the later lines by one):
  `watchGRPCStream.run` (the `Canceled` case, lines 620–629: `close(ws.recvc)` for a substream
  still in `substreams`), `dispatchEvent` (724–742: a response with no events, watch id `-1` and
  a revision is broadcast), `broadcastResponse` (745–753: `select { case ws.recvc <- wr: case
  <-ws.donec: }` for every substream in `substreams`), `watcher.RequestProgress` (413–444).
- **What happens**: a substream whose watch context was canceled exits (`serveSubstream`
  returns, closes `donec`, and blocks on `closingc`) but stays in `substreams` until `run` takes
  it from `closingc`. Meanwhile:
  1. an event for its id cannot be dispatched (`donec` is closed), so `run` sends a cancel
     request for the id;
  2. the server answers it with a `Canceled` response (etcd's `recvLoop` does), and `run`, finding
     the id in `substreams`, closes the substream's `recvc`; the substream is still in
     `substreams`;
  3. the application calls `RequestProgress` (on any context with the same outgoing metadata, so
     on the same gRPC stream); etcd answers with a progress response of watch id `-1` (when every
     watcher of the stream is synced), which `run` broadcasts to every substream:
     `broadcastResponse` selects between a send on the closed `recvc` and a receive on the
     closed `donec`: if Go picks the send, **`panic: send on closed channel`** in `run`'s
     goroutine, which is not recovered: the process crashes.

  No stream failure is needed: a watch canceled with events in flight, followed closely by a
  progress request (Kubernetes' API server, for one, requests progress on its watch streams
  periodically), is enough, given the select choices of steps 1–3.

  Reproduction (a test of the package with the fake `pb.WatchClient` of
  `etcd-watch-resume-closing-substream.md`, whose test file must be in the same overlay: it
  defines the fake). Run without touching the tree with `go test -overlay overlay.json -run
  TestWatchProgressAfterServerCancel .` from `client/v3/`, the overlay mapping
  `client/v3/zz_watch_resume_closing_test.go` and `client/v3/zz_watch_progress_cancel_test.go`
  to the two files:

  ```go
package clientv3

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

// One trial: a watch is canceled with an event in flight, the server answers the cancel
// request run() sends (run() closes the substream's recvc, the substream still registered),
// and a progress request's broadcast response (watch id -1) reaches run() before the closing
// substream does: broadcastResponse selects between a send on the closed recvc and the
// closed donec.
func progressTrial() (int, error) {
	fc := &fakeWatchClient{streams: make(chan *fakeWatchStream, 4)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c)
	ctx, cancel := context.WithCancel(context.Background())
	chc := make(chan WatchChan, 1)
	go func() { chc <- w.Watch(ctx, "a") }()
	s1 := <-fc.streams
	if _, err := waitSent(s1); err != nil {
		return 0, err
	}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 1, Created: true}}
	s1.gate <- struct{}{}
	<-chc
	go w.RequestProgress(context.Background())
	if _, err := waitSent(s1); err != nil {
		return 1, err
	}
	cancel()
	ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("a"), ModRevision: 2}}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Events: []*mvccpb.Event{ev}}}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	r, err := waitSent(s1)
	if err != nil || r.GetCancelRequest() == nil {
		return 2, errTrialLost
	}
	// The server answers the cancel; a progress request waits on reqc.
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Canceled: true}}
	go w.RequestProgress(context.Background())
	time.Sleep(settle)
	s1.gate <- struct{}{}
	if r, err := waitSent(s1); err != nil || r.GetProgressRequest() == nil {
		return 3, errTrialLost
	}
	// The server answers the progress request as etcd's does when every watcher is synced:
	// a response with watch id -1 and no events, broadcast by the client.
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: -1}}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	time.Sleep(settle)
	return 4, errTrialLost
}

// TestWatchProgressAfterServerCancel crashes the test binary with "panic: send on closed
// channel" (watch.go, broadcastResponse) once the scheduler picks the interleaving above.
func TestWatchProgressAfterServerCancel(t *testing.T) {
	var lost [8]int
	for i := 0; i < 3000; i++ {
		st, err := progressTrial()
		lost[st]++
		if err != errTrialLost {
			t.Fatal(err)
		}
	}
	t.Logf("no panic; trials lost at each stage: %v", lost)
}
  ```

  Output at the pinned revision (three runs of three crashed, each in its first trials):

  ```
  panic: send on closed channel
  	/shared/etcd/client/v3/watch.go:747
  	/shared/etcd/client/v3/watch.go:738 +0x26b
  ```
  (`watch.go:747` is `broadcastResponse`'s send, `738` `dispatchEvent`'s call of it.)
- **Expected**: `RequestProgress` is safe to call at any time (its documentation states no
  restriction); a canceled substream is never sent to.
- **How the proof handles it**: `watcher.RequestProgress` is not verified (its calls can make
  `run` panic, so no spec of it holds), and the derived watcher contract
  (`isEtcdRangeWatcher`, `notes/STATUS.md`, "W-C") is for a watcher on which no progress request
  is sent: `run`'s invariant keeps every request it sent a create or a cancel, and the server's
  stream specification sends a response of watch id `-1` only in answer to a progress request.
- **Possible fixes**: in the `Canceled` case, remove the substream from `substreams` when its
  `recvc` is closed (`closeSubstream` then finds nothing to delete), or do not close `recvc` there
  for a substream that is already `closing`; or have `broadcastResponse`/`unicastResponse` skip a
  substream marked closed.
- **Found**: 2026-10-15, the watch slice's unit W-C (`run`'s invariant: a substream in
  `substreams` whose `recvc` is closed must receive nothing more; the per-id case is the server's
  (no response for an id after its `Canceled`), the broadcast case is not).
