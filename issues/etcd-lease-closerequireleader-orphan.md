---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22094 issue open: this issue
  - etcd-io/etcd#22291 pr open: fix (delete the entry when every subscription required a leader); verified in pr-verify/etcd-22291
  - etcd-io/etcd#22253 pr open: equivalent fix (compact, then delete when no channel is left); verified in pr-verify/etcd-22253
  - etcd-io/etcd#22097 pr closed: earlier attempt, closed by its author
---

# client/v3: closeRequireLeader leaves an orphaned keep-alive entry

- **Status**: a bug (a lease kept alive forever, by a client none of whose subscribers wants it).
- **Where**: `client/v3/lease.go` at 09669450f (`etc/goose.py`'s etcd pin), `lessor.closeRequireLeader`
  (`lease.go:383-418`), called by `recvKeepAliveLoop` on `ErrNoLeader` (`lease.go:486`).
- **What happens**: when every subscription of a `keepAlive` was made with
  `WithRequireLeader`, the function closes all its channels and compacts `chs`/`ctxs` to
  length 0, but leaves the entry in `l.keepAlives`. Nothing removes an entry with no channel:
  `keepAliveCtxCloser` removes an entry only when it removes the last channel itself, and the
  subscribers' closers do not find their contexts any more. `sendKeepAliveLoop` keeps sending
  keep-alives for it; `recvKeepAlive` refreshes its `deadline` on every response but advances
  `nextKeepAlive` only inside its loop over `ka.chs`, so the entry is due on every iteration of the
  send loop (every `retryConnWait`, 500ms) once the leader is back, and `deadlineLoop` never reaps it.
  The lease is never let expire, so whatever is attached to it (a `concurrency.Session`'s keys:
  locks, election keys) is never released while the client runs. Reproduction: the PR's test
  `TestLessorCloseRequireLeaderRemovesOrphanedKeepAlive` (`client/v3/lease_requireleader_internal_test.go`
  on etcd-io/etcd#22291's head 71d57990b) fails on the pin and on upstream f744d457f.
- **Expected**: a keep-alive whose subscribers are all gone stops (as `keepAliveCtxCloser` does
  when the last subscriber cancels).
- **How the proof handles it**: the lessor's lock invariant (`lessor.muInv`,
  `Proof/go_etcd_io/etcd/client/v3/InvLease.lean`, on branch `pr-verify/etcd-22291`) says every
  entry has at least one subscription; `lessor.closeRequireLeader` is proved against it at the
  PR's code only. It is not translated with a body on `lean`.
- **Possible fixes**: etcd-io/etcd#22291 or #22253 (both verified to keep the invariant:
  `notes/pr-verify/etcd-22291.md` on `pr-verify/etcd-22291`, `notes/pr-verify/etcd-22253.md` on
  `pr-verify/etcd-22253`).
- **Found**: 2026-10-17, verifying etcd-io/etcd#22291 (the bug the PR fixes).
