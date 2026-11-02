---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#20221 issue closed: related, different trigger: a watch from a future revision got old events through a lagging member's progress notification (closed by #20229)
  - etcd-io/etcd#20229 pr merged: the server check (no progress while a watcher's start revision is above the store's); does not cover a progress computed before the watch was registered
  - etcd-io/etcd#20263 pr closed: proposed a client check on the resume revision going below the start; closed on the belief that #20229 makes it unreachable, which the reproduction below contradicts
  - etcd-io/etcd#15248 pr merged: the client's resume revision from a progress notification (the line that lowers it here)
blocks-proof: yes
---

# clientv3: after a reconnect, a watch from a future revision can deliver events below its start revision

A Go client watch created with `WithRev(r)` for a revision `r` above the store's current one can,
after its stream reconnects, deliver events below `r`. The watch first receives a progress
notification at the store's revision (below `r`), the client moves the watch's resume revision down
to it, and the reconnect re-creates the watch from there.

**Expected:** a watch from revision `r` should deliver no event below `r`: `WithRev` "specifies ...
the start revision of 'Watch' request"
([op.go](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/op.go#L378-L380)).

**Impact:** clients that watch from a future revision on a stream on which progress is requested
(`RequestProgress` on the same client, as Kubernetes' API server does), and whose stream then fails
transiently (`Unavailable`: a member restart, a dropped connection). The progress notification below
the start revision reaches the watch through
[etcd-watch-progress-before-created](etcd-watch-progress-before-created.md) (#20229 stops the other
known trigger, a lagging member); a fix of either closes this path. Reproduced at `main` with one
member.

**Reproduction:** `TestWatchResumeBelowStartRevision` in
[`issues/etcd-watch-resume-below-start-revision/watch_resume_below_start_test.go`](etcd-watch-resume-below-start-revision/watch_resume_below_start_test.go),
copied into `tests/integration/clientv3/watch` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 linux/amd64. One
member behind a bridge; per trial a fresh watcher with a busy prefix watch, `RequestProgress`, then
`Watch("k", WithRev(rev+100))`; on a progress below the start, put `k` and drop the connections.

```
$ go test ./integration/clientv3/watch/ -run '^TestWatchResumeBelowStartRevision$' -count=1
--- FAIL: TestWatchResumeBelowStartRevision (0.41s)
    watch_resume_below_start_test.go:57: trial 2: the watch from revision 161 received a progress notification at revision 62
    watch_resume_below_start_test.go:67: after a reconnect, the watch from revision 161 delivered an event at revision 92 (the put at 92)
FAIL
```

**Cause:** on a progress notification, `serveSubstream` sets the resume revision to the
notification's revision plus one, and stores it as the watch's start for a reconnect, whether or not
that is below the watch's own start revision
([L862-L871](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L862-L871));
the reconnect re-creates the watch from it
([`newWatchClient`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/watch.go#L928-L972)).

## Proof

yes: the verified fork carries the fix (`2e2dc077c`, the cherry-pick of `16f73d6eb` on the fork's
branch `watch-resume-fixes`: the resume revision only moves forward); the watch contract (every event
at or above the start revision) holds across a reconnect only over it
(`Proof/go_etcd_io/etcd/client/v3/WatchResume.lean`, `watchGRPCStream__serveSubstream.lean`).

## Fix

Move the resume revision only forward in `serveSubstream` (`else if wr.Header.Revision+1 > nextRev`),
as the fork's `16f73d6eb` does (with a fake-server regression test,
`client/v3/watch_resume_below_start_test.go`); no upstream fix branch.

## Notes

The user asked (2026-10) whether this is real or only a client hardening: it is real against etcd's
own server at `main`, but only through the server ordering bug above; with that fixed, the client
change is defense in depth, which #20263's closing suggests the maintainers may not want. Kept as its
own file (a second root cause, in the client); flagged for review.
