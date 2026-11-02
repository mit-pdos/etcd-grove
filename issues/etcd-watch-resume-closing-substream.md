---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21969 issue closed: same root cause (a Canceled response closes the watch's channel but leaves it registered), different trigger (a progress broadcast, not a reconnect); closed as stale
  - etcd-io/etcd#22191 pr open: same root cause; its fix (drop the watch from the stream's map when its channel is closed) also keeps a reconnect from resuming it, though the PR does not mention the reconnect path
blocks-proof: yes
---

# clientv3: a reconnect right after a watch is canceled can crash the client with "send on closed channel"

The Go client panics (`send on closed channel` in its watch goroutine, not recovered: the process
exits) when its watch stream fails with a transient error (`Unavailable`) after the member has
answered the cancel of a watch whose context was canceled with an event in flight, and before the
client has torn that watch down: the reconnect resumes the canceled watch and delivers its new
created response on the watch's closed channel. Rare (a transient stream failure at the wrong
moment), but reachable in a long-lived client where canceling a watch's context is the normal way to
stop it.

**Reproduction:** `TestWatchResumeClosingSubstream` in
[`issues/etcd-watch-resume-closing-substream/watch_resume_closing_test.go`](etcd-watch-resume-closing-substream/watch_resume_closing_test.go),
copied into `client/v3` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28),
go1.27.3 linux/amd64. A fake `pb.WatchClient` (through the public `NewWatchFromWatchClient`) plays
the member: the created response, an event after the watch's context is canceled, the `Canceled`
answer to the client's cancel request, an `Unavailable` stream error, then the created response on the
new stream; up to 3000 trials.

```
$ go test . -run '^TestWatchResumeClosingSubstream$' -count=1
panic: send on closed channel
goroutine 485 [running]:
go.etcd.io/etcd/client/v3.(*watchGRPCStream).unicastResponse(...)
	client/v3/watch.go:761
go.etcd.io/etcd/client/v3.(*watchGRPCStream).dispatchEvent(0x1f5ab5a68a90, 0x1f5ab5e05880)
	client/v3/watch.go:741 +0x1ee
go.etcd.io/etcd/client/v3.(*watchGRPCStream).run(0x1f5ab5a68a90)
	client/v3/watch.go:606 +0x51f
FAIL	go.etcd.io/etcd/client/v3	5.200s
```

## Proof

yes: the verified fork carries the fix of
[etcd-watch-progress-closed-substream](etcd-watch-progress-closed-substream.md) (`107edf7e4`, as
#22191), which keeps the canceled watch out of the reconnect; the reconnection is verified over the
fixed code (`notes/decisions.md`, D25).

## Notes

Separate from etcd-watch-progress-closed-substream because the trigger and the crash site differ
(a reconnect and `unicastResponse`, not a progress broadcast); one fix covers both. A fix that drops
the watch must also reset its ID:
[etcd-watch-resume-stale-canceled-id](../nonissues/etcd-watch-resume-stale-canceled-id.md).
