---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22094 issue open: same bug (an emptied keepAlive entry stays and is renewed forever)
  - etcd-io/etcd#22097 pr closed: fix, closed unmerged
  - etcd-io/etcd#22253 pr open: fix (delete the entry when no subscriber is left)
  - etcd-io/etcd#22291 pr open: fix, same approach
  - etcd-io/etcd#22081 issue open: related, a second bug of the same function (issues/etcd-lease-requireleader-ctx-misaligned.md)
---

# client/v3: `lessor.closeRequireLeader` leaves a subscriber-less keep-alive that renews the lease forever

- **Status**: a bug, present at the pin, reproduced (below); also contradicts `Session.Done`'s
  documentation.
- **Where**: `client/v3/lease.go` at `107edf7e4` (`etc/goose.py`'s etcd pin): `closeRequireLeader`
  (lines 383-418) compacts `ka.chs`/`ka.ctxs` to length 0 but never deletes `l.keepAlives[id]`
  (compare `keepAliveCtxCloser`, line 377, and `deadlineLoop`, line 585). `recvKeepAlive`
  refreshes `ka.deadline` unconditionally (line 550) but advances `ka.nextKeepAlive` only inside
  the loop over `ka.chs` (line 563); `sendKeepAliveLoop` sends for every entry whose
  `nextKeepAlive` is past (line 600).
- **What happens**: when every `KeepAlive` subscriber of a lease used `WithRequireLeader` and the
  member reports no leader, all their channels are closed but the entry stays. From then on the
  client sends a `LeaseKeepAliveRequest` for the lease every `retryConnWait` (500 ms); each
  answer refreshes `deadline`, so `deadlineLoop` never reaps it. The lease never expires while
  the client lives. For a `concurrency.Session` created with a require-leader context
  (`WithContext(WithRequireLeader(ctx))`), the session's `Done` closes (the documentation: "when
  the lease is orphaned, expires, or is otherwise no longer being refreshed") while the lease is
  still being refreshed: the session's keys (a `Mutex`'s or an `Election`'s key) stay, and other
  contenders wait until the client closes.

  Reproduction at the pin (an internal test of `client/v3`,
  `issues/etcd-lease-requireleader-orphan-entry/close_require_leader_orphan_test.go`; it fails with
  "entry kept with 0 subscribers"):

  ```go
  func TestCloseRequireLeaderOrphanEntry(t *testing.T) {
  	l := &lessor{keepAlives: make(map[LeaseID]*keepAlive), donec: make(chan struct{})}
  	l.keepAlives[1] = &keepAlive{
  		chs:   []chan<- *LeaseKeepAliveResponse{make(chan *LeaseKeepAliveResponse, 1)},
  		ctxs:  []context.Context{WithRequireLeader(context.Background())},
  		nextKeepAlive: time.Now(), donec: make(chan struct{}),
  	}
  	l.closeRequireLeader()
  	if ka, ok := l.keepAlives[1]; ok {
  		t.Errorf("entry kept with %d subscribers", len(ka.chs))
  	}
  }
  ```
- **Expected**: an entry with no subscriber is removed, as `keepAliveCtxCloser` does; no
  keep-alive is sent for a lease no local caller keeps alive.
- **How the proof handles it**: the lessor is not translated; callers assume `isEtcdLease`
  (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1121`), which says nothing of renewal or
  expiry (`notes/decisions.md`, "Leases without liveness": "a session that ends is observed
  through `Done`"). The recipes' safety results (`mutex_exclusion`, `election_exclusion`,
  `Proof/go_etcd_io/etcd/client/v3/concurrency/Results.lean`) are unaffected: a lease renewed
  for too long only delays others.
- **Possible fixes**: after compacting, `if len(newChs) == 0 { delete(l.keepAlives, id) }`
  (iterate with the key) (#22253, #22291).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#22094 (`notes/bug-triage/etcd-22094.md`).
