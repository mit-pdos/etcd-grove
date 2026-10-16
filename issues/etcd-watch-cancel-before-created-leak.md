---
upstream: none
checked: 2026-10-16
links:
  - etcd-io/etcd#9416 issue closed: same symptom (a canceled Watch leaves its server-side watcher until the next event on its range); its fix #11850 covers only substreams already registered, not those canceled before their Created response
  - etcd-io/etcd#11850 pr merged: the fix of #9416 (cancel request in run's closingc case when ws.id != InvalidWatchID)
---

# A watch canceled before its `Created` response leaks its server-side watcher

- **Status**: bug (a resource leak: a server-side `mvcc` watcher and its stream entry outlive the
  client's watch until an event on its range arrives, which may never happen). Reproduced at the
  pin by a Go test.
- **Where**: `client/v3/watch.go` at the etcd pin of `etc/goose.py` (`107edf7e4`):
  `watchGRPCStream.run`'s `closingc` case (`:688-710`: a cancel request only `if ws.id !=
  InvalidWatchID`), `closeSubstream` (`:499-508`: a substream not yet registered is replaced by
  `nil` in `resuming`), the `Created` case of `run` (`:601-618`: `if ws := w.resuming[0]; ws != nil`,
  so a `Created` for a closed head registers nothing and sends nothing), and the default case
  (`:638-665`: a cancel is sent only when an *event* for the unknown id arrives).
- **What happens**: `Watch(ctx, key)` posts its request, and `run` sends the create request (the
  head of `resuming`). Suppose `ctx` is canceled before the server's `Created` response arrives.
  `serveSubstream` returns and `run` takes the substream from `closingc`. Its id is still
  `InvalidWatchID`, so no cancel is sent, and `closeSubstream` sets `resuming[0] = nil`. Then the
  server's `Created` response for watch id `X` arrives. `resuming[0]` is `nil`, so `run` drops it
  and moves on. The server's watcher `X` is live on the stream, and the client never cancels it
  unless some later event for `X`'s range reaches the default case. This is the leak of #9416
  (`etcd_debugging_mvcc_watcher_total` grows), narrowed to cancellations that race with creation.
  A client that watches with short-lived contexts (a watch with a timeout, a canceled request
  context) while the stream stays open (any other watch on the same context key) accumulates
  server watchers on ranges that are not written to. Reproduction: a test of package `clientv3`,
  with a fake `pb.WatchClient`,
  `issues/etcd-watch-cancel-before-created-leak/watch_cancel_before_created_test.go`. It fails at
  the pin on every run. The control test (cancel after `Created`) passes. Its test function (the
  fakes and `nextSent` are in the file):

  ```go
  func TestWatchCancelBeforeCreatedLeaksServerWatcher(t *testing.T) {
  	s := &fakeWatchStream{sent: make(chan *pb.WatchRequest, 16), resps: make(chan *pb.WatchResponse)}
  	w := &watcher{remote: &fakeWatchClient{s}, streams: make(map[string]*watchGRPCStream), lg: zap.NewNop()}
  	defer w.Close()

  	go w.Watch(context.Background(), "a") // keeps the stream open; created as id 0
  	if r := nextSent(s); r == nil || r.GetCreateRequest() == nil {
  		t.Fatalf("expected create for a, got %v", r)
  	}
  	s.resps <- &pb.WatchResponse{Header: &pb.ResponseHeader{}, WatchId: 0, Created: true}

  	ctx2, cancel2 := context.WithCancel(context.Background())
  	done := make(chan WatchChan)
  	go func() { done <- w.Watch(ctx2, "b") }()
  	if r := nextSent(s); r == nil || string(r.GetCreateRequest().GetKey()) != "b" {
  		t.Fatalf("expected create for b, got %v", r)
  	}
  	cancel2() // canceled before the server's Created response
  	<-done
  	time.Sleep(200 * time.Millisecond)

  	s.resps <- &pb.WatchResponse{Header: &pb.ResponseHeader{}, WatchId: 1, Created: true}
  	if r := nextSent(s); r == nil || r.GetCancelRequest().GetWatchId() != 1 {
  		t.Errorf("no cancel request for server watch 1 of a canceled Watch (got %v): it leaks", r)
  	}
  }
  ```

  At the pin: `no cancel request for server watch 1 of a canceled Watch (got <nil>): it leaks`.
- **Expected**: canceling a watch's context cancels the watch on the server (the behavior #9416
  asked for and #11850 implemented for established watches). The `Watch` documentation (`watch.go:72-73`) says
  "The context `ctx` MUST be canceled, as soon as watcher is no longer being used, to release
  the associated resources".
- **How the proof handles it**: the specs admit it. `watchGRPCStream.run.spec`
  (`Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean`) says nothing about the requests
  `run` must send. Its model's step for a `Created` response with a closed head,
  `RunSt.answer S m i X null false` (`Proof/go_etcd_io/etcd/client/v3/WatchClientModel.lean:757`),
  adds `X` to `regs` without a substream and without a cancel, and no invariant conjunct rules that
  state out. A leaked server resource is outside partial correctness (class C-perf;
  `notes/bug-triage/etcd-9416.md`, proposal `watch-client-cancel-reaches-server`).
- **Possible fixes**: in the `Created` case, when `w.resuming[0] == nil`, send a cancel request
  for `pbresp.WatchId` and add it to `cancelSet`, as the default case does for an unknown id. Or
  keep closed-but-pending substreams in a set and cancel their ids when `Created` arrives.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#9416 (`notes/bug-triage/etcd-9416.md`),
  reading `WatchClientModel.lean`'s `answer` with a `null` head.
