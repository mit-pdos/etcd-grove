---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#10131 issue closed: related, different (2019): watchers stopped recovering and resuming streams seemed to hang after permission-denied refusals; never diagnosed, not this teardown hang
  - etcd-io/etcd#14296 pr merged: related, different: the server answers a refused create with `WatchId` -1; `addSubstream`'s refusal path, which this hang follows, comes from it
---

# `watcher.Close` can hang after the server refuses a watch's create

- **Status**: bug (a hang: `Close` never returns, nor does the refused watch's `Watch`), in the same
  code at upstream `main` and at the pinned `upamanyus/etcd` `a8a459955`. Reproduced (3 runs of 3,
  within 6 trials). Not fixed: a liveness bug, outside what the proofs (partial correctness)
  state; the watch client's verification does not depend on it.
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `8a24be2a3`: `addSubstream` (466–477: a
  refused create, `WatchId == -1` or canceled with a reason, closes the substream's `recvc` and
  registers it nowhere), `run`'s `Created` case (601–618: `w.resuming[0] = nil`), `run`'s
  teardown (520–541: it closes and waits for the substreams in `substreams`, `resuming` and
  `closing` only, then `w.wg.Wait()`), `serveSubstream`'s exit (800–809: `w.closingc <- ws`, then
  `w.wg.Done()`).
- **What happens**: the server refuses a create (etcd answers `Created` and `Canceled` with a
  reason, e.g. `permission denied` when auth does not let the user read the key):
  1. `run` closes the substream's `recvc` and drops it from `resuming`: it is now in none of
     `substreams`, `resuming`, `closing`;
  2. the substream's goroutine sees its `recvc` closed, exits, and waits to post on `closingc`;
  3. `run` stops before it takes that post (here `Close` cancels the stream's context; also a
     halting stream error, or the last other substream closing); its teardown does not count the
     refused substream, so nothing receives its `closingc` post, the goroutine never calls
     `wg.Done()`, and `run` waits in `w.wg.Wait()` forever: `donec` is never closed, so `Close`
     (`<-w.donec`) and the refused watch's `Watch` (its select on `retc`, `ctx.Done()`, `donec`) block
     forever.

  Reproduction (a test of the package with a fake `pb.WatchClient` playing the server; its stream's
  `Send` blocks until the test releases it). Run with `go test -overlay overlay.json -run
  TestWatchCloseAfterRefusedCreate .` from `client/v3/`, the overlay mapping
  `client/v3/zz_close_hang_test.go` to this file:

  ```go
  package clientv3

  import (
  	"context"
  	"testing"
  	"time"

  	"go.uber.org/zap"
  	"google.golang.org/grpc"

  	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
  )

  type refuseStream struct {
  	grpc.ClientStream
  	ctx  context.Context
  	sent chan *pb.WatchRequest
  	gate chan struct{}
  	recv chan *pb.WatchResponse
  }

  func (s *refuseStream) Send(r *pb.WatchRequest) error {
  	s.sent <- r
  	select {
  	case <-s.gate:
  	case <-s.ctx.Done():
  	}
  	return nil
  }

  func (s *refuseStream) Recv() (*pb.WatchResponse, error) {
  	select {
  	case r := <-s.recv:
  		return r, nil
  	case <-s.ctx.Done():
  		return nil, s.ctx.Err()
  	}
  }

  type refuseClient struct{ streams chan *refuseStream }

  func (c *refuseClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
  	s := &refuseStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), gate: make(chan struct{}, 16),
  		recv: make(chan *pb.WatchResponse, 16)}
  	c.streams <- s
  	return s, nil
  }

  // TestWatchCloseAfterRefusedCreate: the server refuses a create (as etcd does when the watch is
  // not permitted); run closes the substream's recvc and forgets it (resuming[0] = nil), and the
  // substream's goroutine then waits to post on closingc. If run stops (Close) before it takes it,
  // its teardown neither counts nor receives it, and waits in wg.Wait() forever: Close hangs.
  func TestWatchCloseAfterRefusedCreate(t *testing.T) {
  	for i := 0; i < 2000; i++ {
  		fc := &refuseClient{streams: make(chan *refuseStream, 1)}
  		c := &Client{}
  		c.lg.Store(zap.NewNop())
  		w := NewWatchFromWatchClient(fc, c)
  		chc := make(chan WatchChan, 1)
  		go func() { chc <- w.Watch(context.Background(), "a") }()
  		s := <-fc.streams
  		<-s.sent
  		s.gate <- struct{}{}
  		// a progress request keeps run busy (its Send blocks) while the refusal arrives
  		go w.RequestProgress(context.Background())
  		<-s.sent
  		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: -1, Created: true,
  			Canceled: true, CancelReason: "etcdserver: permission denied"}
  		time.Sleep(time.Millisecond)
  		// release run: it takes the refusal; close the watcher meanwhile
  		done := make(chan struct{})
  		s.gate <- struct{}{}
  		go func() { w.Close(); close(done) }()
  		select {
  		case <-done:
  		case <-time.After(2 * time.Second):
  			t.Fatalf("trial %d: watcher.Close() hangs", i)
  		}
  		<-chc
  	}
  }

  ```

  Output at `a8a459955` (3 runs of 3):

  ```
  zz_close_hang_test.go:77: trial 4: watcher.Close() hangs
  --- FAIL: TestWatchCloseAfterRefusedCreate (2.01s)
  ```
- **Expected**: `Close` returns once every watch is torn down; a refused watch's `Watch` returns a
  closed channel (with the cancel reason).
- **How the proof handles it**: not at all: the specs are partial correctness, so a teardown that
  waits forever satisfies them. Recorded here as a finding of the reconnection's verification
  (D25), which read `run`'s teardown.
- **Possible fixes**: in `run`'s `Created` case, when `addSubstream` refuses the substream, add it
  to `closing` (as the `Canceled` case does after closing a `recvc`), so that the teardown waits
  for its `closingc` post.
- **Found**: 2026-10-20, designing the reconnection's verification (D25: which substreams `run`'s
  teardown waits for across a reconnect).
