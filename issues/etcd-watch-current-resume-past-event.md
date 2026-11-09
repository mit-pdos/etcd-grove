---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#15248 pr merged: related: the client's resume revision from a watch's responses (the code this bug is in)
blocks-proof: no
---

# clientv3: after a reconnect, a watch from the current revision delivers an event committed before the watch

A Go client watch without `WithRev` (from the current revision) can, after its stream reconnects
before any event arrives, deliver the events of the revision the store was at when the watch was
created: writes that happened before the server received the watch request. One member, a put,
a watch, a dropped connection are enough; it happens every time.

**Expected:** a watch from the current revision should deliver only "watch events that happen
after the server receives the watch request", as
[`Watcher.Watch`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/client/v3/watch.go#L66-L69)
documents.

**Impact:** every client that watches from "now" (no `WithRev`) and whose watch stream fails
transiently before the first event (a member restart, a dropped connection, a load balancer idle
timeout). The watcher sees a stale change as new: for a "wait for the key to change" pattern, a
wake-up for a change that predates the wait. With concurrent writes between the member's
registration of the watch and its reading of the store revision, the same resume can instead skip
events (racy; not reproduced).

**Reproduction:** `TestWatchFromCurrentRevisionResumeDeliversPastEvent` in
[`issues/etcd-watch-current-resume-past-event/watch_current_resume_test.go`](etcd-watch-current-resume-past-event/watch_current_resume_test.go),
copied into `tests/integration/clientv3/watch` at
etcd-io/etcd@ea8b59433d82e8fc3f1365618740395e0028bd03 (2026-10-16), go1.27.3 linux/amd64 (one
member behind a bridge: put `k`, watch `k` with `WithCreatedNotify`, drop the connections):

```
$ (cd tests && go test ./integration/clientv3/watch -run TestWatchFromCurrentRevisionResumeDeliversPastEvent -count=1)
    watch_current_resume_test.go:46: after a reconnect, the watch created at revision 2 delivered an event at revision 2 ("before-the-watch"), committed before the watch
FAIL
```

**Cause:** the server registers a watch from revision 0 at its store's current revision `R`
(events from `R + 1`) and answers with a creation response whose header is the store's revision
`H ≥ R`. On that creation response the client sets the watch's resume revision to `H`
([L855-L860](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/client/v3/watch.go#L855-L860)),
not `H + 1`; a reconnect re-creates the watch from `H`
([`newWatchClient`](https://github.com/etcd-io/etcd/blob/ea8b59433d82e8fc3f1365618740395e0028bd03/client/v3/watch.go)),
and the server sends revision `H`'s events. The comment there explains why the resume revision is
taken from the header at all (a write after `Watch` returns must not be missed); `H + 1` would
lose events of revisions in `(R, H]` instead, so the header alone does not carry enough: the
server would have to report the revision it registered the watch at.

## Proof

no: the client watch spec states the weaker guarantee the code has: a watch from the current
revision is complete only from its first event on, and every event above the creation's header is
delivered (`Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`, `WatchPos.init`'s `floor`).

## Fix

The server's creation response would carry the revision the watch was registered at (or the
member would read the header revision under the same lock as the registration), and the client
would resume from it plus one. No fix branch.

## Notes

Found by batch 1b of the specs-only branch (2026-11-09); the deterministic case confirmed by its
provability review. `gh search` of etcd-io/etcd returned nothing for it (the search may not have
reached GitHub).
