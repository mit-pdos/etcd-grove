# Which issues matter most to etcd's developers

A triage of every file in this directory (2026-10-18): the order in which we would bring the
findings to etcd's and raft's maintainers, by how much they matter to them and how likely they
are to act. Criteria, roughly in this order:

1. **Severity**: a violation of a core guarantee (lost or wrong committed data, linearizability,
   leader or lock uniqueness, watch events skipped) > a crash a client or a normal operational
   event can cause > a wrong result in a less central feature > metrics, logging, documentation.
2. **Reachability**: with the default configuration, through the public API or normal operations
   (failures, restarts, compaction, membership changes); and whether the file has a reproduction.
3. **Upstream**: an open issue or PR with maintainers' interest makes a finding actionable; a
   maintainer's earlier refusal makes it less so; a new finding with a test and a small fix is the
   easiest to bring.
4. **Fix size**: a small local fix with a test is far likelier to be merged than a redesign.

The upstream state of each file is its front matter (`etc/issues-status.py`); this ranking
goes stale as it changes. Re-rank when a finding is added or its upstream state moves.

## Report privately first

The top two let one client take the whole cluster down permanently, every member crashing again
on the WAL replay at restart. They belong in etcd's private security process (security@etcd.io)
before any public issue.

## Top tier: core guarantees or the cluster's availability, with the default configuration

1. **[etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md)**: one client
   transaction (a from-key delete, then a put of the key with `IgnoreValue` or `IgnoreLease`)
   panics every member, and again on every restart. Reproduced end to end (integration test,
   `etcdctl`). Fix: about one line in `checkIntervals`. Upstream: etcd-io/etcd#22395 has the
   same fix but does not mention the panic and calls itself "not a security fix"; what this adds
   is the severity.
2. **[etcd-auth-useradd-long-name-fatal](etcd-auth-useradd-long-name-fatal.md)**: a `UserAdd` or
   `RoleAdd` whose name is over 32 KiB hits bbolt's `ErrKeyTooLarge`, which is fatal on every
   member and again on replay; with auth off (the default) any client can send one. Fix: a length
   check. Confirmed end to end through gRPC (2026-10-18, upstream `main`: `etcdctl user add` or
   `role add` with a 32769-byte name; all three members exit, and again when restarted together).
   Same cause (bbolt errors made fatal in `unsafePut`, one size check covers all three):
   [etcd-auth-record-too-large-fatal](etcd-auth-record-too-large-fatal.md),
   [etcd-backend-put-value-too-large-fatal](etcd-backend-put-value-too-large-fatal.md).
3. **[etcd-compaction-delete-then-put](etcd-compaction-delete-then-put.md)**: compacting at the
   revision that deleted and re-put a key deletes the live value; an acknowledged write is lost
   and members exit on its next read. Reproduced through gRPC and `etcdctl`. Known:
   etcd-io/etcd#22376 and fix PR #22377 are open (a regression from #18274); the useful step is
   to support that PR.
4. **[election-campaign-key-check](election-campaign-key-check.md)**: `Election.Campaign`
   returns success after its own key was deleted (the session's lease expired in a partition, or
   a sibling resigned), so two campaigners both lead: the leader-election API's one guarantee.
   Integration test on the fork branch; fix small (the key check `Mutex.Lock` already does).
   Users reported it twice (etcd-io/etcd#11051, #11777), both closed by the stale bot, not by a
   maintainer. File together with
   **[mutex-lock-recreated](mutex-lock-recreated.md)** (`Mutex.Lock` succeeds while another
   session holds the lock; narrower, two `Mutex` values on one session, but the v3lock service
   reaches it when a client retries a `Lock`).
5. **[etcd-watch-progress-before-created](etcd-watch-progress-before-created.md)**: a progress
   notification can reach a new watch before its catch-up events, so clients that trust progress
   (Kubernetes' watch cache, etcd's `cache`) skip events. Deterministic integration test on the
   fork branch (20 of 20 at 22cc5d9ac); fixed in our fork; searched upstream: not reported
   (related: #15220, fixed by #15237); candidate drafted. Fix: small (a bounded drain).

## Second tier: real, narrower or partly known

6. **[etcd-compact-past-raft-applied](etcd-compact-past-raft-applied.md)**: the apply loop
   snapshots and compacts raft's in-memory log before `Advance` has moved raft's `applied`, so a
   campaign in that window panics the member (`hasUnappliedConfChanges`: "unavailable due to
   compaction"). Default configuration: a follower restarted without a disk snapshot replays its
   log in one `Ready`, and a `MoveLeader` to it (as rolling restarts do) panics it; reproduced on
   `main` with a failpoint widening the window (4 of 4 runs), not yet measured without one. One
   member crashes, a restart recovers it. Fix: small (`applyAll` waits for `raftAdvancedC` before
   snapshotting; tested, `fix.patch`). Upstream: none for this trigger (etcd-io/etcd#9079, the same
   panic from another cause; #18825 made the in-memory snapshot reachable with defaults).
7. **[etcd-watch-progress-closed-substream](etcd-watch-progress-closed-substream.md)**, with
   [etcd-watch-resume-closing-substream](etcd-watch-resume-closing-substream.md) (the same cause):
   the client library panics on a send to a closed channel (for Kubernetes, the API server).
   etcd-io/etcd#22191 has the fix, open with no review; the value is in reviving it.
8. **[etcd-client-retry-put-ctx-error](etcd-client-retry-put-ctx-error.md)**: the retry
   interceptor can resend a `Put`/`Txn`/`Delete` after a `Canceled` status, applying the write
   twice. Less reachable than the file suggests (mostly through proxies or load balancers).
   etcd-io/etcd#18424 was closed as unreachable; the since-merged #21122 undercuts that, a reason
   to reopen.
9. **[raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md)** (one finding
   in four files, with [raft-document-confchange-before-advance](raft-document-confchange-before-advance.md),
   [raft-track-confchange-application](raft-track-confchange-application.md),
   [etcd-leader-advance-before-applyconfchange](etcd-leader-advance-before-applyconfchange.md)):
   `Advance` before `ApplyConfChange`, which the documentation allows, lets two different entries
   commit at the same index. The highest severity of all, but reproduced only on raft's
   `RawNode`; etcd's path is unconfirmed (concurrent membership changes, a slow apply loop, a
   partition). The documentation fix and etcd's five-line change are easy to argue for; claiming
   etcd is affected needs more evidence.
10. **[raft-readindex-singleton-stale](raft-readindex-singleton-stale.md)**: stale linearizable
   reads after shrinking to a single voter. Patch with tests ready; in etcd it needs a contrived
   sequence (scale-down to one member, lost messages, a read right after the election).
11. **[cache-ready-after-retry](cache-ready-after-retry.md)**: after one watch retry the new
    `cache` package never becomes ready again. Deterministic test, fix one line; an actively
    developed package, the likeliest to be merged quickly. Also small and ready:
    **[etcd-range-sort-none-limit](etcd-range-sort-none-limit.md)** (`etcdctl get
    --sort-by=VERSION --limit=1` returns the wrong key; fix branch exists), with
    [etcd-rangestream-sort-none](etcd-rangestream-sort-none.md) (the same `IsDefaultOrdering`
    cause).

Next, if time allows: [raft-snapshot-during-apply-stale-confchange](raft-snapshot-during-apply-stale-confchange.md)
(a wrong follower configuration; the track patch above fixes it too),
[leasing-modify-uncached-once](leasing-modify-uncached-once.md) (every write of an uncached key
committed twice; deterministic, one condition, but see leasing below),
[etcd-apply-lease-checkpoint-sections](etcd-apply-lease-checkpoint-sections.md) (leases outlive
their TTL after a crash in a small window; the fix changes the `Lessor` interface),
[etcd-unary-interceptor-learner-removed](etcd-unary-interceptor-learner-removed.md) (known, PRs
open), [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md) with
[recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md) (one fix branch),
[cache-stale-progress-compacts-newest-watch](cache-stale-progress-compacts-newest-watch.md),
[raft-prevote-stale-grant](raft-prevote-stale-grant.md) (disruption, not safety),
[raft-stale-term-appresp-index-zero-ack](raft-stale-term-appresp-index-zero-ack.md) (a needless
log resend or snapshot to a caught-up follower after a delayed stale-term message; upstream's
`TestLeaderAppResp` pins the behavior),
[etcd-request-id-member-prefix](etcd-request-id-member-prefix.md) (needs two member ids equal in
their low 16 bits),
[etcd-lease-close-require-leader-ctx-misaligned](etcd-lease-close-require-leader-ctx-misaligned.md)
(a canceled `KeepAlive` closes another caller's channel after an `ErrNoLeader` stream end; test and
one-token fix).

## Already in maintainers' hands

[etcd-range-keys-only-lease](etcd-range-keys-only-lease.md) (etcd-io/etcd#22209, labeled for
v3.7.4; a maintainer is discussing the fix's design) and
[etcd-backend-duplicate-put-stale-read](etcd-backend-duplicate-put-stale-read.md)
(etcd-io/etcd#21986, fix PRs open; an etcd caller reaches it: `monitorStorageVersion`'s
v3.5→v3.7 migration writes `meta/storageVersion` three times in one session, and `StorageVersion()`
reads the old value until the next commit, at most about 100 ms; reproduced at the fork pin, our
fork carries #21987).

## Probably not worth their time now

- **Leasing** ([leasing-update-stale](leasing-update-stale.md),
  [leasing-evictrange-key](leasing-evictrange-key.md),
  [leasing-wait-rescind-no-delete](leasing-wait-rescind-no-delete.md),
  [leasing-stale-entry-after-reset](leasing-stale-entry-after-reset.md),
  [leasing-get-failed-acquire-options](leasing-get-failed-acquire-options.md),
  [leasing-evalcmp-missing-key](leasing-evalcmp-missing-key.md)): real, but the package is
  lightly maintained, etcd-io/etcd#20704 was closed by the stale bot, and #21869 (the same fix as
  `leasing-evictrange-key`) was closed under the AI-contribution policy. If filed, one umbrella
  issue with small PRs rather than six issues.
- **Internal-API preconditions etcd never violates**:
  [etcd-alarm-activate-none-zero-fatal](etcd-alarm-activate-none-zero-fatal.md),
  [etcd-auth-newauthstore-nil-tp](etcd-auth-newauthstore-nil-tp.md),
  [etcd-auth-tls-info-assert](etcd-auth-tls-info-assert.md),
  [etcd-auth-token-md-empty](etcd-auth-token-md-empty.md),
  [etcd-lessor-revoke-rd-unlocked](etcd-lessor-revoke-rd-unlocked.md),
  [etcd-lessor-revoke-twice-no-deleter](etcd-lessor-revoke-twice-no-deleter.md),
  [etcd-index-compact-overlapping](etcd-index-compact-overlapping.md),
  [etcd-txn-empty-requestop](etcd-txn-empty-requestop.md),
  [etcd-stream-interceptor-err-before-done](etcd-stream-interceptor-err-before-done.md).
- **Raft-library edge cases unreachable from etcd**:
  [raft-joint-empty-transition-panic](raft-joint-empty-transition-panic.md) and
  [raft-unknown-transition-panic](raft-unknown-transition-panic.md) (one class: `stepLeader` does
  not validate the conf changes it accepts),
  [raft-changer-nil-incoming](raft-changer-nil-incoming.md),
  [raft-config-clone-autoleave](raft-config-clone-autoleave.md),
  [raft-zero-max-size-per-msg](raft-zero-max-size-per-msg.md),
  [raft-memorystorage-createsnapshot-bounds](raft-memorystorage-createsnapshot-bounds.md),
  [raft-memorystorage-initialstate-unlocked](raft-memorystorage-initialstate-unlocked.md),
  [raft-joiner-empty-confstate](raft-joiner-empty-confstate.md),
  [raft-confstate-unknown-fields-panic](raft-confstate-unknown-fields-panic.md) (a mixed-version
  panic, hypothetical until a field is added).
- **Model or documentation only**: [raft-commit-lost-with-entries-kept](raft-commit-lost-with-entries-kept.md),
  [raft-ready-messages-read-after-handout](raft-ready-messages-read-after-handout.md),
  [raft-step-writes-caller-message](raft-step-writes-caller-message.md),
  [etcd-txn-nested-compare-snapshot](etcd-txn-nested-compare-snapshot.md),
  [etcd-max-txn-ops-nested](etcd-max-txn-ops-nested.md),
  [stm-serializable-snapshot](stm-serializable-snapshot.md),
  [recipes-pqueue-dequeue-order](recipes-pqueue-dequeue-order.md),
  [etcd-client-dialoptions-unary-interceptor](etcd-client-dialoptions-unary-interceptor.md)
  (a cheap switch to `WithChainUnaryInterceptor` would likely be accepted),
  [etcd-featuregate-enabled-panic-undocumented](etcd-featuregate-enabled-panic-undocumented.md)
  (the `FeatureGate` interface omits the panic its implementation documents; a one-line doc fix),
  [etcd-robustness-model-equal-mutates](etcd-robustness-model-equal-mutates.md) (test code: the
  robustness model's `Equal` sorts its arguments, against porcupine's contract; harmless, a cheap
  fix).
- **Absurd configurations or sizes**: [etcd-compactor-periodic-tiny-retention](etcd-compactor-periodic-tiny-retention.md),
  [etcd-watch-progress-interval-overflow](etcd-watch-progress-interval-overflow.md),
  [etcd-compaction-negative-batch-limit](etcd-compaction-negative-batch-limit.md) (a cheap fix
  nonetheless).
- **Declined, unreproduced or out of scope**:
  [etcd-txn-check-intervals-sibling](etcd-txn-check-intervals-sibling.md) (maintainers declined:
  #16380 closed not planned),
  [etcd-backend-read-buffer-cache-stale-after-commit](etcd-backend-read-buffer-cache-stale-after-commit.md)
  (deterministic, a one-line fix, but no wrong etcd result known),
  [etcd-watch-sync-ticker-reset-zero](etcd-watch-sync-ticker-reset-zero.md) (Windows only; known,
  PR open), [etcd-watch-id-reuse-stale-events](etcd-watch-id-reuse-stale-events.md) (not
  reproduced), [etcd-compactor-started-before-start](etcd-compactor-started-before-start.md) (not
  reproduced), [etcd-request-id-zero-bootstrap-confchange](etcd-request-id-zero-bootstrap-confchange.md)
  (a member started in one particular millisecond), [go-itab-reinterpret-assert](go-itab-reinterpret-assert.md)
  (Go, not etcd).
- **Metrics**: [etcd-apply-alarm-gauge-reactivate](etcd-apply-alarm-gauge-reactivate.md),
  [etcd-apply-authstatus-metric-label](etcd-apply-authstatus-metric-label.md) (trivial fixes, easy
  merges, little impact).

## How to bring them

Each report or PR should be reviewed and submitted by a person, with its Go reproduction test
first (a maintainer closed etcd-io/etcd#21869 under the AI-contribution policy). The drafts and
fix branches are made by `.claude/skills/upstream-report`.
