---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#22191 pr open: its fix (drop the watch from the stream's map when its channel is closed) introduces this bug: the dropped watch keeps its ID; unreviewed, labeled stale
  - etcd-io/etcd#21981 pr closed: the same fix as #22191 (would introduce this bug too); closed unmerged
  - etcd-io/etcd#21969 issue closed: the panic #22191 fixes (issues/etcd-watch-progress-closed-substream.md); closed as stale
  - etcd-io/etcd#21069 pr closed: related, different: watch IDs unique per member (would remove this bug's precondition, IDs reused across streams); closed unmerged
blocks-proof: yes
---

# clientv3 (with #22191): after a reconnect, a server-canceled watch's stale ID can delete the resumed watch that reuses it

With #22191's fix applied, a watch the member has canceled is dropped from the stream's map but keeps
its ID; if the stream reconnects before the client tears that watch down, another watch resumed on the
new stream can get the same ID, and the teardown then deletes (or cancels at the member) that other
watch: it receives no more events and its channel is never closed, and `Close` can hang.

**Why not an issue:** only in the code of an unmerged pull request (#22191, and the verified fork);
at `main` the same window is the panic of
[etcd-watch-resume-closing-substream](../issues/etcd-watch-resume-closing-substream.md). Kept here
rather than with the PR's work because the verified fork carries #22191's fix, so the proof meets it.

**Test:** `TestWatchResumeStaleCanceledID` in
[`nonissues/etcd-watch-resume-stale-canceled-id/watch_resume_stale_id_test.go`](etcd-watch-resume-stale-canceled-id/watch_resume_stale_id_test.go)
(from the fork's `04375baaa`), copied into `client/v3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef with #22191's diff (`gh pr diff 22191`, head
34aa7c606) applied, go1.27.3 linux/amd64:

```
$ go test . -run '^TestWatchResumeStaleCanceledID$' -count=1
--- FAIL: TestWatchResumeStaleCanceledID (2.13s)
    watch_resume_stale_id_test.go:200: trial 20: the resumed watch lost its event (run deleted it under the canceled watch's stale id); trials lost at each stage: [0 0 0 2 8 0 10 1]
FAIL
```

## Proof

yes: the verified fork carries #22191's fix and this one on top (`cafce83d8`, from `04375baaa` on
branch `watch-resume-fixes`: reset the dropped watch's ID to `InvalidWatchID`); the reconnection's
proof is over it (`Proof/go_etcd_io/etcd/client/v3/WatchClientModel.lean`).

## Notes

For #22191: one line in its `Canceled` case (`ws.id = InvalidWatchID` after the delete), or have
`closeSubstream` delete `substreams[ws.id]` only when it is `ws`. Worth a review comment on #22191 if
it moves.
