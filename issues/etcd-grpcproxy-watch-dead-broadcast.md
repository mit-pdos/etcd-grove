---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#18231 issue closed: the existing watchers' half (the server cancels the backend watch, the proxy's clients wait for ever); closed by the stale bot, unfixed
  - etcd-io/etcd#21813 issue open: the new watchers' half (add and coalesce put watchers into the dead broadcast); does not mention the nextrev reset to 1
  - etcd-io/etcd#21814 pr open: stopped flag, guards add and coalesce, re-attaches the dead broadcast's watchers to a live or new broadcast (re-watching); fixes both halves
  - etcd-io/etcd#21930 pr closed: an earlier fix of #21813 along the same lines (closed unmerged)
  - etcd-io/etcd#21881 pr open: related, different (a re-established backend watch's second Created is forwarded); cites #18231 as possibly related
  - etcd-io/etcd#19296 issue closed: related, different trigger (an expired token ends the backend watch; "both watchers hang" is this mechanism)
---

# grpcproxy: a watch broadcast whose backend watch ends stays in use, silently

One file for etcd-io/etcd#18231 and #21813: they are one defect. Both are the proxy's
`newWatchBroadcast` goroutine leaving its loop when the backend watch channel closes, with no
re-watch, no `Canceled` to its receivers and no mark that the broadcast is dead.
#18231 is what that does to the broadcast's existing watchers; #21813 is what it does to
watchers that arrive later. The same change fixes both (#21814 re-attaches a dead broadcast's
watchers, which re-watches, and keeps new ones out). A proof of the goroutine fails at the same
point for both: the loop's exit.

- **Status**: a bug (watchers through the gRPC proxy stop receiving events, without an error,
  after their backend watch ends). Not in translated code: `server/proxy/grpcproxy` has no
  `Code/` module.
- **Where** (etcd pin `107edf7e4`, `server/proxy/grpcproxy/`):
  - `watch_broadcast.go:55-76` (`newWatchBroadcast`'s goroutine: `for wr := range wch {
    wb.bcast(wr); update(wb) }`, then only `close(wb.donec)`; the broadcast stays in
    `watchBroadcasts.bcasts`);
  - `watch_broadcast.go:79-93` (`bcast`: `wb.nextrev = wr.Header.Revision + 1` once
    `responses > 0`);
  - `watch_broadcast.go:97-128` (`add`) and `watch_broadcasts.go:53-83` (`coalesce`): check
    `nextrev` and `responses` only, never whether the goroutine is alive;
  - `watcher.go:106-109` (`watcher.send` drops a response with no events, not `Created`, not a
    progress notification and `CompactRevision == 0`, so a `Canceled` response never reaches the
    proxy's client);
  - the backend watch is the verified client's: `client/v3/watch.go:487-498`
    (`closeSubstream`: on a stream error, a last `WatchResponse{Header: &pb.ResponseHeader{},
    Canceled: true}`, then the channel closes; on a server cancel the channel closes after the
    cancel response).
- **What happens**: when the server cancels the backend watch or the backend stream fails, the
  goroutine exits. Its receivers get nothing further, and their streams stay open (#18231). The
  client's final `Canceled` response has header revision 0, so `bcast` sets the dead broadcast's
  `nextrev` to 1 (a detail not in the upstream reports). From then on `add` puts into it every
  new watcher of the range that starts at revision 1 or later, emulating a `Created` for it, and
  `coalesce` moves into it the watchers of a live broadcast of the range that has fewer than 5
  receivers (any `nextrev >= 1`, and the dead one has `responses > 0`), stopping the live one (#21813). None of them gets
  another event. Reproduction at the pin, with a fake backend `Watcher`:
  `issues/etcd-grpcproxy-watch-dead-broadcast/dead_broadcast_test.go` (dropped into
  `server/proxy/grpcproxy/`; `go test ./proxy/grpcproxy/ -run
  TestWatchBroadcastDeadAfterBackendClose -v` from `server/`). It passes at the pin: after the
  backend channel closes, the first watcher receives nothing and no new `Watch` is made;
  `nextrev` is 1; a watcher from revision 3 joins the dead broadcast (with an emulated
  `Created`); a current watcher's new broadcast is coalesced into the dead one.
- **Expected**: the proxy keeps the server's watch guarantee for its clients: a watcher receives
  every event of its range from its start revision, in order, or a `Canceled` response. When a
  backend watch ends, the proxy re-watches from the broadcast's `nextrev` (or cancels its
  receivers), and a dead broadcast takes no new watchers.
- **How the proof handles it**: out of scope. `server/proxy/grpcproxy` is not translated (no
  `Code/` module, no function in the verified-code inventory). The one verified function on the
  path, the backend client's `watcher.Watch`, allows what happens: its channel "may be closed"
  (`Spec/go_etcd_io/etcd/client/v3/watcher__Watch.lean:31`, the `isSpsc … rangeWatchElem`
  postcondition at line 45), and a consumer that wants every event must handle the close. The
  proxy does not. Triage: `notes/bug-triage/etcd-18231.md`, `notes/bug-triage/etcd-21813.md`
  (proposal `grpcproxy-watch-relay`: the invariant "every broadcast in `bcasts` has a live
  goroutine" fails at the goroutine's exit at the pin).
- **Possible fixes**: on the loop's exit, mark the broadcast stopped under `wb.mu`, remove it from
  `bcasts`, and re-add its receivers through `watchBroadcasts.add` (a new backend watch from each
  receiver's `nextrev`) — the shape of #21814; `add` and `coalesce` skip a stopped broadcast.
  Independently, do not let a response with a zero header revision (the client's synthetic
  `Canceled`) move `nextrev` backwards in `bcast`. Alternatively, re-watch in a loop inside the
  goroutine, as the #18231 reporter suggests, while the proxy's context is live.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#18231 and etcd-io/etcd#21813.
