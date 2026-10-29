# Which issues matter most to etcd's developers

A triage of every file in this directory (2026-10-18, the files added since placed 2026-10-20, the
watch-resume findings re-ranked 2026-10-21, the fork's fixes of the alarm store's race and the
snapshot file's release noted 2026-10-22, the msgappv2 decoder's lengths added 2026-10-22; upstream states as of 2026-10-21): the order in which we would bring the
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
goes stale as it changes. Re-rank when a finding is added or its upstream state moves. The findings
we have already filed ourselves (issues and PRs by `upamanyus` or `upamanyus-agent`) are out of
the tiers, in "Filed by us" below, whatever their severity: what remains to do for them is to see
the filing through, not to decide whether to bring it.

## Report privately first?

etcd's threat model trusts its clients (2026-10-21): a crash a client can cause with a request it
is allowed to send is a robustness bug, not a security issue, and does not go to security@etcd.io
on that ground alone. [etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md) (item
1) takes the whole cluster down permanently; it crosses a permission line only with auth enabled,
where a user allowed to write one key can crash every member. Whether it goes through the private
process or publicly through etcd-io/etcd#22395 was the user's decision: a security report
(2026-10-21), to be safe and to try etcd's security process.

## Top tier: core guarantees or the cluster's availability, with the default configuration

1. **[etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md)**: one client
   transaction (a from-key delete, then a put of the key with `IgnoreValue` or `IgnoreLease`)
   panics every member, and again on every restart. Reproduced end to end (integration test,
   `etcdctl`). Fix: about one line in `checkIntervals`. Upstream: etcd-io/etcd#22395 has the
   same fix but does not mention the panic and calls itself "not a security fix"; what this adds
   is the severity.
2. **[etcd-compaction-delete-then-put](etcd-compaction-delete-then-put.md)**: compacting at the
   revision that deleted and re-put a key deletes the live value; an acknowledged write is lost
   and members exit on its next read. Reproduced through gRPC and `etcdctl`. Known:
   etcd-io/etcd#22376 and fix PR #22377 are open (a regression from #18274); the useful step is
   to support that PR.
3. **[etcd-watch-progress-before-created](etcd-watch-progress-before-created.md)**: a progress
   notification can reach a new watch before its catch-up events, so clients that trust progress
   (Kubernetes' watch cache, etcd's `cache`) skip events. Deterministic integration test on the
   fork branch (20 of 20 at 22cc5d9ac); fixed in our fork; searched upstream: not reported
   (related: #15220, fixed by #15237); candidate drafted. Fix: small (a bounded drain).

## Second tier: real, narrower or partly known

4. **[etcd-compact-past-raft-applied](etcd-compact-past-raft-applied.md)**: the apply loop
   snapshots and compacts raft's in-memory log before `Advance` has moved raft's `applied`, so a
   campaign in that window panics the member (`hasUnappliedConfChanges`: "unavailable due to
   compaction"). Default configuration: a follower restarted without a disk snapshot replays its
   log in one `Ready`, and a `MoveLeader` to it (as rolling restarts do) panics it; reproduced on
   `main` with a failpoint widening the window (4 of 4 runs), not yet measured without one. One
   member crashes, a restart recovers it. Fix: small (`applyAll` waits for `raftAdvancedC` before
   snapshotting; tested, `fix.patch`). Upstream: none for this trigger (etcd-io/etcd#9079, the same
   panic from another cause; #18825 made the in-memory snapshot reachable with defaults).
5. **[etcd-watch-progress-closed-substream](etcd-watch-progress-closed-substream.md)**, with
   [etcd-watch-resume-closing-substream](etcd-watch-resume-closing-substream.md) (the same cause):
   the client library panics on a send to a closed channel (for Kubernetes, the API server).
   etcd-io/etcd#22191 has the fix, open with no review and labeled stale 2026-10-24 (the bot
   closes it within weeks unless someone acts); the value is in reviving it, with
   [etcd-watch-resume-stale-canceled-id](etcd-watch-resume-stale-canceled-id.md), which must go
   with it: the fix keeps the canceled substream's id, so after a reconnect a resumed watch that
   reuses the id is deleted by the old substream's teardown: it silently gets no more events, its
   channel never closes, and `Close` can hang (the last substream). The worst failure a watch can
   have (a cache or controller on it keeps a stale view), not in `main` today but introduced by
   the PR as it stands (and by our fork's K0 until F1); reproduced within 5 to 54 trials. A
   one-line addition to the PR: reset the id.
6. **[etcd-client-retry-put-ctx-error](etcd-client-retry-put-ctx-error.md)** (deferred,
   2026-10-21: it turns on what at-most-once etcd's client promises, to take up separately): the retry
   interceptor can resend a `Put`/`Txn`/`Delete` after a `Canceled` status, applying the write
   twice. Less reachable than the file suggests (mostly through proxies or load balancers).
   etcd-io/etcd#18424 was closed as unreachable; the since-merged #21122 undercuts that, a reason
   to reopen.
7. **[raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md)** (one finding
   in two files, with
   [etcd-leader-advance-before-applyconfchange](etcd-leader-advance-before-applyconfchange.md)):
   `Advance` before `ApplyConfChange`, which the documentation allows, lets two different entries
   commit at the same index. The highest severity of all, but reproduced only on raft's
   `RawNode`; etcd's path is possible and no etcd check prevents it, only timing (investigated
   2026-10-23: concurrent membership changes, a slow apply loop, a partition), not reproduced on a
   cluster. The documentation fix and etcd's five-line change are easy to argue for; claiming
   etcd is affected in practice needs more evidence.
8. **[etcd-quota-stale-backend-after-snapshot](etcd-quota-stale-backend-after-snapshot.md)**
    (not in the current filing list, 2026-10-21: availability, the user prefers safety findings)
    (2026-10-19): the gRPC quota check keeps the backend it saw at startup, so after a member
    installs a leader's snapshot it judges writes by its old, closed backend; if that one was over
    the quota, every write through the member re-raises NOSPACE for the whole cluster, through
    compaction, defragmentation and disarming, until the member restarts. Default configuration,
    the documented NOSPACE recovery with one member down during it; reproduced by an integration
    test at the pin; fix a few lines (tested). Searched upstream 2026-10-20: not reported
    (related: #20553, the same stale backend in the maintenance `Defragment` path, fixed).
9. **[etcd-auth-snapshot-closed-backend-panic](etcd-auth-snapshot-closed-backend-panic.md)**
    (2026-10-19): with auth enabled, `applySnapshot` closes the old backend before
    `authStore.Recover`, so a serializable read, watch, keep-alive, `Authenticate` or admin RPC
    reaching a member as it installs a leader's snapshot panics it on a nil bolt read tx. One
    member crashes and a restart recovers it. Reproduced end to end at the pin (7 of 10 runs) and
    on `main` (3 of 3). The fix moves the close after the stores' recovery (tested, applies to
    `main`). Searched upstream: not reported (the shutdown variant was #17223).
10. **[etcd-merged-snapshot-stale-term](etcd-merged-snapshot-stale-term.md)** (2026-10-19): a
    leader that steps down while saving a Ready (a slow disk) can later send a queued `MsgSnap`
    stamped with its old term but carrying data of a newer term, which a follower still at the old
    term installs; with a gap of two terms, a leader of the term in between can panic (`need
    non-empty snapshot`). Needs a stall longer than an election timeout, two followers past
    compaction and a partition (5 or more members, asymmetric); the etcd half reproduced with the
    real apply loop, the panic in raft from hand-built messages, not end to end. With a gap of one
    term no wrong result was found (one untraced consequence: a `--force-new-cluster` restart of
    that follower writes log terms that go down); no wrong commit was found with any gap. Fix a few
    lines (merge only at the message's term; tested; the verified fork carries it). Searched
    upstream 2026-10-19: not reported (raft#47 states the invariant).
11. **[etcd-txn-empty-serializable](etcd-txn-empty-serializable.md)** (2026-10-20): a `Txn`
    with comparisons and no operations counts as serializable (`IsTxnSerializable` is vacuously
    true), so a member that is behind answers it from its local state without the read index: a
    stale verdict and revision, a linearizability violation of a public request. Rare in practice
    (compare-only transactions), by inspection only, no reproduction yet; the fix is a one-line
    guard. Upstream not searched yet.

12. **[etcd-applied-index-stale-after-snapshot](etcd-applied-index-stale-after-snapshot.md)**
    (2026-10-26): after a follower installs a leader's snapshot, `applySnapshot` leaves the atomic
    applied index behind (only `applyEntries` sets it), and the request limit (committed > applied
    + 5000) then refuses every write through that member until another member's write commits; in
    a quiet cluster indefinitely. Default configuration (`SnapshotCatchUpEntries` 5000); reproduced
    by an integration test at the pin, which a one-line fix passes. Availability through one
    member, no data loss. Upstream not searched beyond `main`'s code (unchanged).

13. **[etcd-auth-grant-permission-same-key](etcd-auth-grant-permission-same-key.md)**
    (2026-10-27): `RoleGrantPermission` on a range the role has updates it only if it is the first
    permission with its key; else it appends a duplicate and the old type stays in effect (a
    downgrade from `READWRITE` to `READ` leaves writes permitted). Needs two permissions sharing a
    key; admin-only with auth on; reproduced by a unit test at the pin; a small fix (match the
    range end too). Upstream not searched.

Also to file (2026-10-21, the last scan of the current batch):
[etcd-watch-id-reuse-stale-events](etcd-watch-id-reuse-stale-events.md) (a watch created with a
client-chosen id that a just-canceled watch used receives the canceled watch's buffered events, of
another key; reproduced at upstream `main`, 80 of 80 runs; the auto-assigned-id variant is not
reproduced; candidate drafted; it was listed here as "not reproduced" until 2026-10-21, which was
wrong), [raft-memorystorage-initialstate-unlocked](raft-memorystorage-initialstate-unlocked.md)
(a data race `-race` reports: `InitialState` reads and, in v3.7, writes `MemoryStorage`'s fields
without its documented mutex; the fix takes the lock) and
[etcd-alarm-store-snapshot-race](etcd-alarm-store-snapshot-race.md) (above). Not in the batch:
[raft-joint-self-quorum-read](raft-joint-self-quorum-read.md) (liveness, a configuration nobody
runs) and the conf-change validation panics (`raft-joint-empty-transition-panic`,
`raft-unknown-transition-panic`: only the application's own proposals reach them, a trusted
caller's precondition).

Next, if time allows: [raft-snapshot-during-apply-stale-confchange](raft-snapshot-during-apply-stale-confchange.md)
(a wrong follower configuration; the track patch above fixes it too),
[raft-async-snapshot-during-apply-divergence](raft-async-snapshot-during-apply-divergence.md)
(with `AsyncStorageWrites`, the documented thread model lets entries be applied on top of a later
snapshot: a diverged state machine; reproduced, but etcd does not enable the option; fixed by the
`raft-snapshot-during-apply-stale-confchange` candidate),
[leasing-modify-uncached-once](leasing-modify-uncached-once.md) (every write of an uncached key
committed twice; deterministic, one condition, but see leasing below),
[etcd-apply-lease-checkpoint-sections](etcd-apply-lease-checkpoint-sections.md) (leases outlive
their TTL after a crash in a small window; the fix changes the `Lessor` interface),
[etcd-unary-interceptor-learner-removed](etcd-unary-interceptor-learner-removed.md) (known, PRs
open), [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md) with
[recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md) (one fix branch),
[cache-stale-progress-compacts-newest-watch](cache-stale-progress-compacts-newest-watch.md)
(etcd-io/etcd#20229 blocks the lagging-member trigger, but reproduced at upstream `main` on
2026-10-23 with one member and a concurrent `RequestProgress` on the same client, through the
server's unfixed progress-before-`Created` ordering; a spurious `ErrCompacted`, not lost data),
[raft-stale-term-appresp-index-zero-ack](raft-stale-term-appresp-index-zero-ack.md) (a needless
log resend or snapshot to a caught-up follower after a delayed stale-term message; upstream's
`TestLeaderAppResp` pins the behavior),
[etcd-rafthttp-misaddressed-403-member-removed](etcd-rafthttp-misaddressed-403-member-removed.md)
(a peer URL that reaches the wrong member of the same cluster, as after a stale `UpdateMember` or a
reused address, makes the healthy sender stop with "data-dir used by this member must be removed":
`Process`'s `403` for a misaddressed message is the one `checkPostResponse` reads as
`errMemberRemoved`, since etcd-io/etcd#17078, in 3.4 and up; availability only, code path certain,
reachability not reproduced by a test yet, which it needs before filing; #20356 saw such rejections
in a cluster that became unavailable, closed without a root cause),
[etcd-request-id-member-prefix](etcd-request-id-member-prefix.md) (needs two member ids equal in
their low 16 bits),
[etcd-lease-close-require-leader-ctx-misaligned](etcd-lease-close-require-leader-ctx-misaligned.md)
(a canceled `KeepAlive` closes another caller's channel after an `ErrNoLeader` stream end; test and
one-token fix; known: etcd-io/etcd#22081 and fix PR #22087, open, unreviewed, marked stale),
[etcd-alarm-store-snapshot-race](etcd-alarm-store-snapshot-race.md) (2026-10-20: `restoreAlarms`
replaces `s.alarmStore` unsynchronized while `Status`/`/health` read it; the race detector reports
it in 4 of 5 runs of an integration test; effect a stale alarm list for a moment; fixed in our fork
2026-10-22 by the upstream candidate's fix, the store recovered in place, with an integration test
that fails 5 of 5 without it and passes 15 of 15 with it),
[etcd-release-snapdb-before-open](etcd-release-snapdb-before-open.md) (2026-10-20, code reading: a
second snapshot's `Release` can delete the `.snap.db` file `applySnapshot` has not opened yet, a
follower panic; needs two snapshots in quick succession; fixed in our fork 2026-10-22, `Release`
moved after the open, with a deterministic unit test that fails 5 of 5 without the fix and passes
10 of 10 with it; known upstream: etcd-io/etcd#18055, open, reproduced there by the robustness
tests and Antithesis, with fix PR #22046 open, so the useful step is to support that PR, not to
file).

Two of the watch client's resume-path findings (2026-10-20, D25), in this order, which is by how
likely a deployment is to hit them rather than by severity alone:
[etcd-watch-close-hang-refused-create](etcd-watch-close-hang-refused-create.md) (after the server
refuses a watch's create, as auth's permission denied does, a `Close` at the wrong moment hangs
forever; a hang, not a wrong result, but its preconditions are ordinary: auth enabled and a
`Close`; reproduced 3 of 3; small fix) and
[etcd-watch-resume-below-start-revision](etcd-watch-resume-below-start-revision.md) (a wrong
result, the one upstream watch bug here that delivers wrong data: after a reconnect a watch
delivers events below the `WithRev` it asked for, silently, so a caller using the start revision
as a checkpoint re-processes old events; but it needs a start revision in the future of the
store's, which is unusual (watches start at the current revision + 1 or at a past one; Kubernetes'
watch cache does neither), plus a progress notification before that revision and a transient
stream failure; reproduced deterministically against a fake server only, not on a cluster;
one-line fix with a test). The file's server step does not happen as described (2026-10-21): every
supported branch's `progressIfSync` (`main`, release-3.4 to 3.6, the fork pin) sends no progress
to a watcher whose start revision is above the store's (`if rev < w.startRev { return false }`),
so neither `WithProgressNotify` nor `RequestProgress` reaches it directly. A path not yet checked:
a `RequestProgress` broadcast computed before the watch's create, sent (through the watch stream)
after its `Created` (through the control stream), which the client then broadcasts to the new
substream; until one is shown, this is a client hardening for old servers.

## Filed by us

Issues and PRs by `upamanyus` (or `upamanyus-agent`), checked against GitHub 2026-10-21. Ranked by
what is left to do:

1. **[raft-readindex-removed-leader](raft-readindex-removed-leader.md)**: fixed, etcd-io/raft#536
   (merged 2026-10-19 in the reviewer's form, `IsVoter && IsSingleton`). The maintainer reopened our
   issue #534 to track backports and asked us to cherry-pick by hand to raft's release-3.7 and
   release-3.6 and to etcd's release-3.5 (`raft/`), the bot's cherry-picks having conflicts: the
   open action. The reviewer's form leaves
   [raft-joint-self-quorum-read](raft-joint-self-quorum-read.md) (a liveness bug, a read at a
   `{1}&&{1}` leader waits) unfixed, not reported.
2. **[mutex-lock-recreated](mutex-lock-recreated.md)**: reported, etcd-io/etcd#22613 with fix PR
   #22617 (both open, 2026-10-19). `Mutex.Lock` succeeds while another session holds the lock; the
   v3lock service reaches it when a client retries a `Lock`. A maintainer may answer that `Lock`
   returning nil is no guarantee anyway (the session can expire right after it returns) and only
   `IsOwner()` fencing is, which fails correctly here; what sets this apart is that the caller's
   own session is alive and another session's key is live and first when `Lock` returns. Its
   sibling [election-campaign-key-check](nonissues/election-campaign-key-check.md) is not filed (below).
3. **[etcd-range-sort-none-limit](etcd-range-sort-none-limit.md)**: reported, etcd-io/etcd#22612
   with our fix #22616; someone else's fix #22615 was opened an hour earlier, all open. #22615
   changes `IsDefaultOrdering` itself and so would also fix
   [etcd-rangestream-sort-none](etcd-rangestream-sort-none.md); if the maintainers prefer it, ours
   closes. Jefftree (cc'd by serathius) agreed with the problem and fix on the issue (2026-10-21),
   doubting how often it is hit; no PR reviewed yet (2026-10-26).
4. **[cache-ready-after-retry](cache-ready-after-retry.md)**: reported, etcd-io/etcd#22614 (open,
   2026-10-19); no PR of ours, but someone else's #22618 (open, 2026-10-19, `needs-ok-to-test`) is
   our candidate's fix and test verbatim, crediting the report. A one-line fix with a
   deterministic test in an actively developed package, the likeliest quick merge; what is left is
   to support #22618 rather than open a duplicate.
5. **[raft-readindex-singleton-stale](raft-readindex-singleton-stale.md)**: fixed, etcd-io/raft#535
   (merged 2026-10-19, closing our #533); the maintainer sees no need to backport. Nothing left.
6. **[leasing-update-stale](leasing-update-stale.md)**: reported in part, etcd-io/etcd#20704
   (2025-09-23, its bugs 1 and 3 are this finding's cases 3 and 4; cases 1 and 2 are not in it),
   closed by the stale bot, unfixed. Reviving it belongs with the leasing umbrella below.
7. **[bbolt-commit-meta-error-frees-reader-pages](bbolt-commit-meta-error-frees-reader-pages.md)**:
   reported, etcd-io/bbolt#1311 with our fix PR #1312 (both open, filed 2026-10-23). A `Commit` that
   fails after its meta page reached the file frees pages an open read transaction still reads (a
   serializability violation); not reachable through etcd. `ok-to-test` 2026-10-24 and CI green,
   no review yet (2026-10-26). Left to do: see the PR through review.

Earlier filings of ours that the files link as related but not the finding: etcd-io/etcd#19091 and
its fix #19092 (2024-12, the leasing session-expiry stale read, closed unmerged; linked from
`leasing-stale-entry-after-reset`), #21536 (2026-03, the cache's `Get(WithRev)` revision gaps, fixed
by #21540), #20729 (2025-09, merged: the 2^48 event window comment in `idutil`), and
etcd-io/raft#392, #397, #398 (2026-02, `ReadIndex` retries with a reused `rctx`, closed).

## Already in maintainers' hands

[etcd-range-keys-only-lease](etcd-range-keys-only-lease.md) (etcd-io/etcd#22209, labeled for
v3.7.4; a maintainer is discussing the fix's design) and
[etcd-backend-duplicate-put-stale-read](etcd-backend-duplicate-put-stale-read.md)
(etcd-io/etcd#21986, fix PRs open; an etcd caller reaches it: `monitorStorageVersion`'s
v3.5→v3.7 migration writes `meta/storageVersion` three times in one session, and `StorageVersion()`
reads the old value until the next commit, at most about 100 ms; reproduced at the fork pin, our
fork carries #21987). [etcd-rangestream-sort-none](etcd-rangestream-sort-none.md) is fixed by
someone else's open etcd-io/etcd#22615 without saying so (the `IsDefaultOrdering` change, above).
Also [raft-reportsnapshot-finish-not-noop](raft-reportsnapshot-finish-not-noop.md)
(the `ReportSnapshot` comment: etcd-io/raft#243, open, fixes it as part of a breaking v4 change).

## Probably not worth their time now

- **[etcd-quota-backend-bytes-mmap-panic](etcd-quota-backend-bytes-mmap-panic.md)** (2026-10-29):
  a `--quota-backend-bytes` above about 2.5·10^14 (amd64) makes `newBackend`'s 110% mmap exceed
  bbolt's `maxMapSize`, and etcd panics at startup with a message that does not name the flag. An
  operator's absurd setting, loud and immediate; a validation check and a line in the flag's help
  fix it. With a test.
- **[etcd-cfg-watch-progress-interval-race](etcd-cfg-watch-progress-interval-race.md)** (2026-10-26):
  `NewWatchServer` writes `s.Cfg.WatchProgressNotifyInterval` (a sub-100ms setting raised to the
  minimum) while other goroutines read `s.Cfg`; a data race with a non-default setting, benign in
  effect. A small fix (keep the adjusted value out of `s.Cfg`); no reproduction yet.
- **[etcd-auth-readtx-getallroles-panics](etcd-auth-readtx-getallroles-panics.md)** (2026-10-23):
  `(*authReadTx).UnsafeGetAllRoles` panics whenever called (a no-limit range of a non-safe
  bucket on a read transaction); nothing in etcd calls it, so a dead interface method. A one-line
  fix (`UnsafeForEach`, as the users' twin) or a removal; no user impact.
- **[etcd-watch-resume-nil-watch-chan](etcd-watch-resume-nil-watch-chan.md)**: a watch canceled
  while the client reconnects can be handed a nil `WatchChan` (a receive blocks forever); needs
  the caller's goroutine to be late by a whole reconnect. Small fix with a test.

- **[etcd-watch-resume-waitgroup-overflow](etcd-watch-resume-waitgroup-overflow.md)**: a reconnect
  with 2^31 or more watches on one stream panics in `waitCancelSubstreams` (an `int32` wait-group
  counter given `len(w.resuming)` at once). Out of reach in practice (2^31 goroutines); one-line
  fix, no test possible.

- **Leasing** ([leasing-evictrange-key](leasing-evictrange-key.md),
  [leasing-wait-rescind-no-delete](leasing-wait-rescind-no-delete.md),
  [leasing-stale-entry-after-reset](leasing-stale-entry-after-reset.md),
  [leasing-get-failed-acquire-options](leasing-get-failed-acquire-options.md),
  [leasing-evalcmp-missing-key](leasing-evalcmp-missing-key.md), and
  [leasing-update-stale](leasing-update-stale.md) from "Filed by us"): real, but the package is
  lightly maintained, our etcd-io/etcd#20704 was closed by the stale bot, and someone else's #21869
  (the same fix as `leasing-evictrange-key`) was closed under the AI-contribution policy. If
  filed again, one umbrella issue with small PRs rather than six issues.
- **Robustness against a non-etcd peer**:
  [etcd-rafthttp-msgappv2-unbounded-lengths](etcd-rafthttp-msgappv2-unbounded-lengths.md)
  (2026-10-22): the msgappv2 stream decoder allocates whatever entry count and sizes the stream
  says (a panic at `2^63`, or exhaustion), where the other stream codec caps messages at
  `readBytesLimit`; between etcd members the counts are an encoder's, so only a misbehaving peer or
  a corrupted stream reaches it. A small fix (the same `ErrExceedSizeLimit` check); low priority;
  someone else's etcd-io/etcd#21874 (open, stalled) has it, so supporting that PR is the step.
  [etcd-rafthttp-stream-dial-bad-server-version-panic](etcd-rafthttp-stream-dial-bad-server-version-panic.md)
  (2026-10-23): a stream dial's response with a malformed `X-Server-Version` panics the dialing
  member (`semver.MustParse` outside any handler), with a test; between members the header is
  always valid on `main`, but on 3.5/3.6 a `v`-prefixed custom build's is not (etcd-io/etcd#22261).
  A small fix (`semver.NewVersion` and a failed dial); low priority; someone else's
  etcd-io/etcd#21829 (open, unreviewed, needs a rebase) has it.
  [etcd-rafthttp-addremote-bad-peerurls-panic](etcd-rafthttp-addremote-bad-peerurls-panic.md)
  (2026-10-26): a raft request from an id that is no peer with a malformed `X-PeerURLs` makes
  `AddRemote` `Logger.Panic`, which `net/http` recovers (a logged stack, no exit), with a test; a
  log-and-return fix; low priority.
- **Internal-API preconditions etcd never violates**:
  [etcd-alarm-activate-none-zero-fatal](etcd-alarm-activate-none-zero-fatal.md),
  [etcd-auth-token-md-empty](etcd-auth-token-md-empty.md),
  [etcd-auth-simple-token-assign-prefix-panic](etcd-auth-simple-token-assign-prefix-panic.md),
  [etcd-stream-interceptor-err-before-done](etcd-stream-interceptor-err-before-done.md).
- **Raft-library edge cases unreachable from etcd as configured**:
  [raft-remove-last-voter-panic](raft-remove-last-voter-panic.md) (`stepLeader` does not
  validate the conf changes it accepts; of that class, the one etcd can reach, a `member remove`
  of the only member with `--strict-reconfig-check=false`, which panics it at apply and at every
  restart; a self-inflicted loss of the whole cluster, with a one-line refusal in
  `mayRemoveMember` as the etcd fix; etcd-io/etcd#13848 hit the same panic through
  `--force-new-cluster` and was closed not planned),
  [raft-compact-past-snapshot](raft-compact-past-snapshot.md) (added 2026-10-26: `Compact`'s
  documentation omits that the storage's snapshot must cover the compacted prefix; a
  documentation fix, etcd compacts behind a fresh snapshot),
  [raft-config-clone-autoleave](raft-config-clone-autoleave.md) and
  [raft-memorystorage-initialstate-unlocked](raft-memorystorage-initialstate-unlocked.md)
  (candidate rechecked 2026-10-23; the user's choice is to upstream it).
- **Test code**: [etcd-robustness-model-equal-mutates](etcd-robustness-model-equal-mutates.md) (test code: the
  robustness model's `Equal` sorts its arguments, against porcupine's contract; harmless, a cheap
  fix).
- **Absurd configurations or sizes**: [etcd-compactor-periodic-tiny-retention](etcd-compactor-periodic-tiny-retention.md)
  (best raised on open etcd#22396, which bounds the retention but misses this case),
  [etcd-watch-progress-interval-overflow](etcd-watch-progress-interval-overflow.md),
  [etcd-compaction-negative-batch-limit](etcd-compaction-negative-batch-limit.md),
  [etcd-corrupt-check-time-negative-panic](etcd-corrupt-check-time-negative-panic.md) and
  [etcd-downgrade-check-time-negative-spin](etcd-downgrade-check-time-negative-spin.md) (the last
  three one validation PR: `Config.Validate` already rejects the comparable
  `--compact-hash-check-time <= 0`; 2026-10-23; open etcd-io/etcd#22476 would turn the downgrade
  spin into the same startup panic, rechecked 2026-10-26).
- **Not issues**: moved to [nonissues/](nonissues/README.md) on review (2026-10-23), with
  the documentation findings parked there for now: [election-campaign-key-check](nonissues/election-campaign-key-check.md)
  (`not-filing`: `Campaign` returning nil after its own key was deleted is the same as the session
  expiring right after it returns; the guarantee is fencing on the key's create revision, which
  fails correctly), and the preconditions etcd or raft's applications meet, test helpers'
  preconditions (the integration bridge's second `Blackhole`, rafthttp's second `CutPeer` of a
  remote), a raft regression with no realistic trigger
  ([raft-confstate-unknown-fields-panic](nonissues/raft-confstate-unknown-fields-panic.md)),
  raft behavior the review accepted ([raft-prevote-stale-grant](nonissues/raft-prevote-stale-grant.md),
  discussed upstream in 2017), a race only release-3.5 with `--enable-v2` has
  ([etcd-rafthttp-leaderstats-followers-race](nonissues/etcd-rafthttp-leaderstats-followers-race.md),
  moved 2026-10-26) and the documentation-only findings listed there.
- **Client-triggered, with clients trusted**:
  [etcd-auth-useradd-long-name-fatal](etcd-auth-useradd-long-name-fatal.md) (a `UserAdd` or
  `RoleAdd` name over 32 KiB is fatal on every member and again on replay; root-only with auth
  on, and with auth off any client can delete everything anyway; reproduced on `main`; a length
  check), with [etcd-auth-record-too-large-fatal](etcd-auth-record-too-large-fatal.md) and
  [etcd-backend-put-value-too-large-fatal](etcd-backend-put-value-too-large-fatal.md) (the same
  cause, one size check covers all three). Cheap robustness fixes, not a priority for etcd.
- **Declined, unreproduced or out of scope**:
  [etcd-txn-check-intervals-sibling](etcd-txn-check-intervals-sibling.md) (maintainers declined:
  #16380 closed not planned),
  [etcd-backend-read-buffer-cache-stale-after-commit](etcd-backend-read-buffer-cache-stale-after-commit.md)
  (deterministic, a one-line fix, but no wrong etcd result known),
  [etcd-watch-sync-ticker-reset-zero](etcd-watch-sync-ticker-reset-zero.md) (Windows only; known,
  PR open), [etcd-compactor-started-before-start](etcd-compactor-started-before-start.md) (reproduced
  2026-10-27 with a short periodic retention and a delayed `Start`; a small fix, in the fork), [etcd-request-id-zero-bootstrap-confchange](etcd-request-id-zero-bootstrap-confchange.md)
  (a member started in one particular millisecond),
  [raft-switchtoconfig-pending-reads](raft-switchtoconfig-pending-reads.md) (reads postponed to
  the leader's first commit are not released when `switchToConfig`'s commit is that commit; not a
  bug for an application that applies conf changes before `Advance`, so not filing: it is one more
  consequence of the misuse in item 7), [go-itab-reinterpret-assert](go-itab-reinterpret-assert.md)
  (Go, not etcd; a golang/go issue drafted, not filed),
  [go-overlapping-named-array-copy](go-overlapping-named-array-copy.md) (Go's compiler, not
  etcd: a miscompiled overlapping array copy in safe Go; already fixed upstream, golang/go#78371,
  go1.26.2).
- **Metrics**: [etcd-apply-alarm-gauge-reactivate](etcd-apply-alarm-gauge-reactivate.md),
  [etcd-apply-authstatus-metric-label](etcd-apply-authstatus-metric-label.md) (trivial fixes, easy
  merges, little impact).

[etcd-unsafe-range-limit-buffer](etcd-unsafe-range-limit-buffer.md) (2026-10-23): a limited
`ReadTx.UnsafeRange` is a prefix of the range only with no buffered entry in it; its one pager
(`store.restore`) meets that, rechecked on `main` 2026-10-26. A doc line at most today, but
someone else's open etcd-io/etcd#22594 adds a second pager, `syncWatchers`' `rangeEvents` over the
newest revisions (what the read buffer holds), which would miss watch events: a review comment
there, if that PR moves, is worth more than a doc PR.

## bbolt (etcd's storage; none reachable through etcd as configured)

etcd's backend exits on any `Commit` error (`batchTx.commit`: `lg.Fatal("failed to commit
tx")`), bounds requests at 1.5 MiB by default and uses the default page size, so none of these
reaches etcd. For bbolt's own maintainers the order would be:
[bbolt-commit-meta-error-frees-reader-pages](bbolt-commit-meta-error-frees-reader-pages.md)
(MVCC broken after an I/O error, for any user that keeps the `DB` after a failed `Commit`;
reproduced, small fix; filed 2026-10-23 as etcd-io/bbolt#1311 with PR #1312, see "Filed by
us"; bbolt's own failpoint `beforeWriteMetaError` tests this rollback path but fires before
the meta reaches the file, which is the case missed), [bbolt-max-value-size-unusable](bbolt-max-value-size-unusable.md)
(values `Put` accepts make data unreadable; reproduced; the 256 MB variant, etcd-io/bbolt#931,
was fixed; candidate drafted 2026-10-23), [bbolt-large-values-leaf-unreadable](bbolt-large-values-leaf-unreadable.md)
(its sibling split off 2026-10-23: values committed together past 2 GiB on one page panic every
`Get`; candidate drafted, merges cleanly with the previous one),
[bbolt-txstats-unaligned-32bit](bbolt-txstats-unaligned-32bit.md) (a regression on `main`, not
released: every transaction panics on 32-bit platforms; worth reporting before a release ships
it), [bbolt-large-page-size](bbolt-large-page-size.md) (an option check),
[bbolt-fillpercent-nan](bbolt-fillpercent-nan.md) (a NaN `FillPercent` panics `Commit` on amd64; a
one-line clamp fix; added 2026-10-29),
[bbolt-deleted-bucket-handle](bbolt-deleted-bucket-handle.md) (a handle used after its bucket's
`DeleteBucket` in the same transaction panics or silently misses data; documentation or an
error return; added 2026-10-27),
[bbolt-mmap-madvise-leak](bbolt-mmap-madvise-leak.md) (one line; moot if #940 lands).

## Kubernetes (the API server's etcd3 store, its test model, the DaemonSet controller; not etcd's)

For Kubernetes' sig-api-machinery, not etcd's maintainers:
[k8s-correctness-model-noop-rewrite](k8s-correctness-model-noop-rewrite.md) (2026-10-22). The
storage test model `correctness.Model` rejects the store's intended rewrite of non-canonical or
stale data on a no-op update. It is a test-only bug that `TestCorrectness` does not reach, with a
Go reproduction and a small fix in the Model.
[k8s-watchcache-index-error-partial-update](k8s-watchcache-index-error-partial-update.md)
(2026-10-26): the watch cache keeps (and soon serves) an object whose update failed in its
indexer, with no event in its history; reproduced at the store. Only reached through an index
function that fails, which Kubernetes' own do only on an object of the wrong type: worth a small
robustness fix (index before mutating), not urgent.

For sig-apps (the DaemonSet controller):
[k8s-daemonset-ambiguous-create-duplicate-pod](k8s-daemonset-ambiguous-create-duplicate-pod.md)
(2026-10-26): after a pod create that committed but returned an error, the next sync creates a
second pod on the node (the consistency store of KEP-5647 records only successful writes, and the
expectations are lowered). Transient (the extra pod is deleted once the cache sees it), but it
breaks the invariant the controller robustness test of kubernetes/kubernetes#139657 checks, and
that test cannot reach it (its faults never reach the server). Reproduced deterministically on the
real API server with a commit-then-fail fault added to that test (10 of 10), with a tested small
fix (record the listed pods in the consistency store after an ambiguous error); #86140's review
(2019) had accepted extra pods on this path for ReplicaSets, never for DaemonSets. Worth reporting
to sig-apps and the KEP-5647 / #139657 author with the reproduction (draft in `upstream/`).

For sig-api-machinery (client-go's work queue, found verifying it for the DaemonSet controller):
[k8s-workqueue-done-without-get-duplicates](k8s-workqueue-done-without-get-duplicates.md)
(2026-10-27): `Done` for an item that is queued but not being processed (a double `Done`) pushes a
duplicate, after which two workers process the same key concurrently, the one guarantee the queue
gives controllers. A caller bug, but undocumented and easy to write; a one-line guard with a Go
reproduction, worth proposing (with the documentation) after the DaemonSet report.
[k8s-workqueue-exponential-backoff-2to63](k8s-workqueue-exponential-backoff-2to63.md)
(2026-10-27): an off-by-one cap in the exponential limiter gives a negative delay at exactly
`2^63` ns; unreachable with the defaults (5 ms, 1 ms), so low priority, but a one-character fix
with a test.
[k8s-clientgo-getindexers-unlocked-map](k8s-clientgo-getindexers-unlocked-map.md) (2026-10-27):
`GetIndexers` hands out the store's own indexers' map without the lock while `AddIndexers` (allowed
on a started shared informer) writes it under the lock; `go test -race` reproduces it; reached by
`pkg/controller`'s `AddPod*Indexer` on a shared pod informer and by the mutation cache. A
`RLock` + `maps.Clone` fix; worth bringing with the work-queue findings.

## How to bring them

Each report or PR should be reviewed and submitted by a person, with its Go reproduction test
first (a maintainer closed etcd-io/etcd#21869 under the AI-contribution policy). The drafts and
fix branches are made by `.claude/skills/upstream-report`.
