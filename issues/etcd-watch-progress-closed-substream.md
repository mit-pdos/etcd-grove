---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21969 issue closed: this bug (progress broadcast sends on a canceled watch's closed channel); closed as stale (not planned), not fixed
  - etcd-io/etcd#22191 pr open: the fix (drop the watch from the stream's map when its channel is closed); no review, needs-ok-to-test, labeled stale
  - etcd-io/etcd#21981 pr closed: the same fix, closed unmerged
blocks-proof: yes
---

# clientv3: a progress notification right after a watch is canceled can crash the client with "send on closed channel"

The Go client panics (`send on closed channel` in its watch goroutine, not recovered: the process
exits) when a progress notification for the stream arrives after the member has answered the cancel
of a watch whose context was canceled with an event in flight, and before the client has torn that
watch down. No stream failure is needed: canceling watches and calling `RequestProgress` on the same
client (Kubernetes' API server does both) is enough, given the scheduling.

**Reproduction:** `TestWatchProgressAfterServerCancel` in
[`issues/etcd-watch-progress-closed-substream/watch_progress_cancel_test.go`](etcd-watch-progress-closed-substream/watch_progress_cancel_test.go),
copied into `client/v3` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28),
go1.27.3 linux/amd64. A fake `pb.WatchClient` (through the public `NewWatchFromWatchClient`) plays
the member as etcd answers: the created response, an event after the watch's context is canceled, the
`Canceled` answer to the client's cancel request, then a progress response (watch ID -1); up to 3000
trials.

```
$ go test . -run '^TestWatchProgressAfterServerCancel$' -count=1
panic: send on closed channel
goroutine 756 [running]:
go.etcd.io/etcd/client/v3.(*watchGRPCStream).broadcastResponse(...)
	client/v3/watch.go:747
go.etcd.io/etcd/client/v3.(*watchGRPCStream).dispatchEvent(0x14d0bebcc270, 0x14d0bebc4c00)
	client/v3/watch.go:738 +0x26b
go.etcd.io/etcd/client/v3.(*watchGRPCStream).run(0x14d0bebcc270)
	client/v3/watch.go:638 +0x62c
FAIL	go.etcd.io/etcd/client/v3	7.208s
```

## Proof

yes: the verified fork carries the fix (`upamanyus/etcd` `107edf7e4`, from `7fc17d0aa` on the fork's
branch `watch-progress-closed-substream`, the same change as #22191); `run`'s invariant needs a
watch whose channel is closed to be out of the broadcast set
(`Proof/go_etcd_io/etcd/client/v3/InvWatch.lean`, `WatchClientModel.lean`).

## Notes

With #22191 applied at the base (head 34aa7c606), the test no longer panics (4 runs, 3000 trials
each); the package's goroutine-leak check then fails the run on the trials' leftover fake streams,
which the test does not clean up (a cleanup to add before the test goes upstream). #22191's
fix introduces [etcd-watch-resume-stale-canceled-id](../nonissues/etcd-watch-resume-stale-canceled-id.md)
unless it also resets the watch's ID. Same root cause, second trigger:
[etcd-watch-resume-closing-substream](etcd-watch-resume-closing-substream.md).
