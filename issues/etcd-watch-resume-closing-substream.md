---
upstream: known
checked: 2026-10-20
links:
  - etcd-io/etcd#21969 issue closed: same root cause (Canceled response closes recvc but leaves the substream registered), different symptom (progress broadcast, not resume after reconnect); closed as stale
  - etcd-io/etcd#22191 pr open: same root cause; its fix (delete from substreams after close(recvc)) also keeps newWatchClient from resuming the closed substream, though it does not mention the resume path
---

# The watch client resumes a closing substream and can send on its closed `recvc`

- **Status**: bug, fixed in the verified fork (open upstream: etcd-io/etcd#22191 has the same
  root-cause fix): `goose-lean` `107edf7e4` (the fix of
  [etcd-watch-progress-closed-substream](etcd-watch-progress-closed-substream.md)) drops the
  substream from `substreams` when `run` closes its `recvc`, so `newWatchClient` no longer moves
  it into `resuming`. Re-run 2026-10-20 at the pin `8a24be2a3`: the reproduction below no longer
  panics (3000 trials; in the 133 that reached the reconnect, no create was sent for the canceled
  substream; the package's leak check then reports the
  trials' leftover goroutines, which the test does not clean up). The fix leaves the substream's
  id, which a reconnect can make another watch's:
  [etcd-watch-resume-stale-canceled-id](etcd-watch-resume-stale-canceled-id.md) (fixed on the
  fork branch `watch-resume-fixes`).
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `bc8b52a50` (the same code as upstream
  `main`; the pinned `457b8d1b6` adds one line at 868, shifting the later lines by one): `watchGRPCStream.run` (the `Canceled` case, lines 620–629, closes a
  substream's `recvc`; the `errc` case, 666–680, reconnects), `newWatchClient` (928–972: every
  substream, closing or not, goes back to `resuming`; only non-closing ones get a new
  `serveSubstream`), `nextResume` (713–721: picks the head of `resuming`, closing or not), the
  `Created` case (601–618: `addSubstream` then `dispatchEvent`), `unicastResponse` (756–767:
  `select { case ws.recvc <- wr: case <-ws.donec: }`).
- **What happens**: a substream whose goroutine has exited for good (`closing`, e.g. its watch's
  context was canceled: `serveSubstream` returns, closes `donec`, and blocks on `closingc`) stays
  in `substreams` until `run` takes it from `closingc`. Meanwhile:
  1. an event for its id cannot be dispatched (`donec` is closed), so `run` sends a cancel
     request for the id;
  2. the server answers it with a `Canceled` response (etcd's `recvLoop` does), and `run`, finding
     the id in `substreams`, closes the substream's `recvc`;
  3. the stream fails with a transient error (`codes.Unavailable` or `codes.Internal`: not
     `isHaltErr`), and `run` reconnects: `newWatchClient` moves the closing substream (its `id`
     reset) into `resuming`, and `nextResume` sends a create request for it;
  4. the server creates the watch; `run` takes the `Created` response before the substream from
     `closingc` (both ready: Go picks at random), registers the closing substream under the new
     id and calls `dispatchEvent`, whose `unicastResponse` selects between a send on the closed
     `recvc` and a receive on the closed `donec`: if Go picks the send, **`panic: send on closed
     channel`** in `run`'s goroutine, which is not recovered: the process crashes.

  Each of steps 1–4 needs `run`'s select to take a response before the closing substream, so a
  crash needs a transient stream failure at the wrong moment after a watch is canceled with
  events in flight: rare but reachable in a long-lived client (a canceled watch context is the
  normal way to stop a watch; the recipes' `WaitEvents` does it every time).

  Reproduction (a test of the package with a fake `pb.WatchClient` playing the server; the
  stream's `Send` blocks until the test releases it, to make `run` busy while two of its select's
  cases become ready). Run without touching the tree with `go test -overlay overlay.json -run
  TestWatchResumeClosingSubstream .` from `client/v3/`, the overlay mapping
  `client/v3/zz_watch_resume_closing_test.go` to this file:

  ```go
package clientv3

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

// A fake gRPC watch stream; the test plays the server. Send blocks until the test opens the
// gate, so that the test can make run() busy while it readies two of its select's cases.
type fakeWatchStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	gate chan struct{}
	recv chan fakeRecv
}

type fakeRecv struct {
	resp *pb.WatchResponse
	err  error
}

func (s *fakeWatchStream) Send(r *pb.WatchRequest) error {
	s.sent <- r
	select {
	case <-s.gate:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *fakeWatchStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type fakeWatchClient struct{ streams chan *fakeWatchStream }

func (c *fakeWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &fakeWatchStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16),
		gate: make(chan struct{}, 16), recv: make(chan fakeRecv, 16)}
	c.streams <- s
	return s, nil
}

var errTrialLost = errors.New("interleaving not hit")

func waitSent(s *fakeWatchStream) (*pb.WatchRequest, error) {
	select {
	case r := <-s.sent:
		return r, nil
	case <-time.After(100 * time.Millisecond):
		return nil, errTrialLost
	}
}

const settle = 3 * time.Millisecond

var stages [8]int

func oneTrial() (int, error) {
	fc := &fakeWatchClient{streams: make(chan *fakeWatchStream, 4)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c)
	ctx, cancel := context.WithCancel(context.Background())
	chc := make(chan WatchChan, 1)
	go func() { chc <- w.Watch(ctx, "a") }()
	s1 := <-fc.streams
	if _, err := waitSent(s1); err != nil { // the create request
		return 0, err
	}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 1, Created: true}}
	s1.gate <- struct{}{}
	<-chc
	// Make run() busy in a Send (a progress request), then cancel the watch's context (its
	// substream goroutine exits, closing, and waits on closingc) and queue an event for it.
	go w.RequestProgress(context.Background())
	if _, err := waitSent(s1); err != nil {
		return 1, err
	}
	cancel()
	ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("a"), ModRevision: 2}}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Events: []*mvccpb.Event{ev}}}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	// If run() takes the event first, it cannot dispatch it and sends a cancel request.
	r, err := waitSent(s1)
	if err != nil || r.GetCancelRequest() == nil {
		return 2, errTrialLost
	}
	// The server answers the cancel (as etcd's does), then the stream fails transiently. A
	// progress request waits on reqc, so that run() can be made busy again (in its Send) after
	// it takes the canceled response, while the error reaches errc.
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Canceled: true}}
	s1.recv <- fakeRecv{err: status.Error(codes.Unavailable, "transient")}
	go w.RequestProgress(context.Background())
	time.Sleep(settle)
	s1.gate <- struct{}{}
	if r, err := waitSent(s1); err != nil || r.GetProgressRequest() == nil {
		return 3, errTrialLost
	}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	// If run() took the canceled response (closing the substream's recvc) and takes the error
	// before the closing substream, it reconnects and resumes the closing substream.
	var s2 *fakeWatchStream
	select {
	case s2 = <-fc.streams:
	case <-time.After(100 * time.Millisecond):
		return 4, errTrialLost
	}
	if _, err := waitSent(s2); err != nil { // the resumed create request
		return 5, err
	}
	s2.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 2, Created: true}}
	time.Sleep(settle)
	s2.gate <- struct{}{}
	// If run() takes the created response first, unicastResponse selects between a send on
	// the substream's closed recvc (a panic) and its closed donec.
	time.Sleep(settle)
	return 6, errTrialLost
}

// TestWatchResumeClosingSubstream crashes the test binary with "panic: send on closed
// channel" (watch.go, unicastResponse) once the scheduler picks the interleaving above.
func TestWatchResumeClosingSubstream(t *testing.T) {
	for i := 0; i < 3000; i++ {
		st, err := oneTrial()
		stages[st]++
		if err != errTrialLost {
			t.Fatal(err)
		}
	}
	t.Logf("no panic; trials lost at each stage: %v", stages)
}
  ```

  Output at the pinned revision (five runs of five crashed, each in its first few trials):

  ```
  === RUN   TestWatchResumeClosingSubstream
  panic: send on closed channel

  goroutine 37 [running]:
  go.etcd.io/etcd/client/v3.(*watchGRPCStream).unicastResponse(...)
  	/shared/etcd/client/v3/watch.go:761
  go.etcd.io/etcd/client/v3.(*watchGRPCStream).dispatchEvent(0xc4182f13ba0, 0xc4182e00e80)
  	/shared/etcd/client/v3/watch.go:741 +0x1ee
  go.etcd.io/etcd/client/v3.(*watchGRPCStream).run(0xc4182f13ba0)
  	/shared/etcd/client/v3/watch.go:606 +0x51f
  ```
- **Expected**: a closed watch is never resumed; a reconnect resumes only the substreams still
  served (the comment in `newWatchClient` says the closing ones are left to the teardown path).
- **How the proof handles it**: the client's watch is verified under the premise
  `noRetryableStreamErr` (no error of a client stream has the status code `Unavailable` or
  `Internal`, the codes `isHaltErr` lets `run` retry on): every receive error then ends `run`, and
  the reconnection (`newWatchClient` after `errc`, the resume queue, `waitCancelSubstreams`) is
  dead code in the verified behaviour, verified only at its first call; `notes/STATUS.md`, "W-C".
- **Possible fixes**: in `newWatchClient`, skip `closing` substreams when rebuilding `resuming`
  (they are torn down through `closingc` anyway), or skip them in `nextResume`; or have
  `unicastResponse`/`addSubstream` refuse a `closing` substream; or close `recvc` only from one
  place (the substream's own teardown).
- **Found**: 2026-10-15, the watch slice's unit W-C (designing `run`'s invariant: a `Created`
  response is dispatched to the substream at the head of `resuming`, whose `recvc` must be open
  for `unicastResponse`'s send to be safe, and nothing keeps a closing substream out of
  `resuming`).
