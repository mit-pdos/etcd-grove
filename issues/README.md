# Issues found while verifying

One file per issue found in the verified Go code (raft, etcd, their dependencies) or its
documentation: a bug (a reachable panic or wrong result), a precondition the code needs
but its API does not state, or documentation the code contradicts. Not for bugs in this
repository's own specs and proofs (those go in `notes/`).

Name a file `<project>-<short-slug>.md`. It starts with a front-matter block that tracks where the
issue stands upstream (the only place that does; `etc/issues-status.py` lists it, and `--refresh`
updates the linked issues' and PRs' states from GitHub):

```
---
upstream: none
checked: 2026-10-16
links:
  - etcd-io/etcd#22395 pr open: same root cause and fix; does not mention the panic
candidate: issues/upstream/<slug>/
---
```

- `upstream`: `unchecked` (no search of upstream yet), `none` (searched: nothing upstream, not
  reported), `known` (an upstream issue or PR by someone else covers it, in `links`), `reported` (we
  filed it, in `links`), `fixed` (fixed upstream: the PR or commit in `links`), `not-filing` (decided
  not to report; say why in `links` or the body).
- `checked`: when upstream was last searched (or the links refreshed).
- `links`: one line per related upstream issue, PR or commit: `<repo>#<n> <issue|pr> <state>: <how it
  relates>` (state: `open`, `closed`, `merged`), or `<repo>@<sha>: ...` for a commit. Related but
  different issues go here too, saying so.
- `candidate` (optional): the upstream drafts (`.claude/skills/upstream-report`).

Then give it:

- **Status**: what the finding is (a bug, an unstated precondition, documentation; not a bug,
  why), not where it is upstream (the front matter).
- **Where**: the Go code (file:line at the pinned revision in `etc/goose.py`) and the
  documentation involved.
- **What happens**: the behavior, with a reproduction (a Go test, inline or by path) when
  one exists.
- **Expected**: what the documentation or API promises instead.
- **How the proof handles it**: the premise, spec or scope choice that keeps it out of the
  verified results (file:line).
- **Possible fixes**.
- **Found**: date and by what (which proof or check).

`RANKING.md` (not an issue: no front matter, skipped by `etc/issues-status.py`) ranks all of them
by how much they matter to etcd's and raft's maintainers and how likely they are to act; update it
when an issue is added or its upstream state moves.

## Drafts for etcd-io/etcd

The findings of the etcd client-side work (cache, concurrency, leasing, recipes) are written as
drafts of the issues to file against etcd-io/etcd, one per finding (the proofs state what the
code does; a finding is a behaviour the specs could not hide): each names the upstream revision
it refers to, how to reproduce it (a test on the fix branch) and the fix. The fix branches are
on the fork `upamanyus/etcd` (`upamanyus/etcd-raft` for raft), one signed-off commit each off upstream
`main`, with the tests, named `fix/<slug>` (the earlier drafts, off f061acd09, without the prefix); the issues and pull requests are filed by hand from them. A finding that is not a bug
(a documentation request) has no fix branch. A draft covers the fields above in its own order
(summary, what happens, how to reproduce, expected, the fix); "How the proof handles it" is in
`notes/STATUS.md`'s section for the package.

| Draft | Kind | Fork branch | Found in |
|---|---|---|---|
| [cache-ready-after-retry](cache-ready-after-retry.md) | bug | `fix/cache-ready-after-retry` (4c9743e0e test, 27352098d fix, off 22cc5d9ac; pushed) | `cache` (STATUS "The whole package") |
| [mutex-lock-recreated](mutex-lock-recreated.md) | bug | `fix/mutex-lock-recreated` (b28d26713 test, 34adb1693 fix, off 22cc5d9ac; pushed) | `concurrency` (Mutex) |
| [election-campaign-key-check](election-campaign-key-check.md) | bug | `fix/election-campaign-key-check` (91d51234f test, a9699489e fix, off 22cc5d9ac; pushed) | `concurrency` (Election) |
| [stm-serializable-snapshot](stm-serializable-snapshot.md) | documentation | none (`stm-serializable-snapshot` kept local, not proposed) | `concurrency` (STM) |
| [leasing-evictrange-key](leasing-evictrange-key.md) | bug | `leasing-evictrange-key` (14d1c4bf3) | `leasing` (units 1–2) |
| [leasing-evalcmp-missing-key](leasing-evalcmp-missing-key.md) | bug | `leasing-evalcmp-missing-key` (06541aec6) | `leasing` (units 1–2) |
| [leasing-modify-uncached-once](leasing-modify-uncached-once.md) | bug | `leasing-modify-uncached-once` (7a6077dec) | `leasing` (units 3–4) |
| [leasing-get-failed-acquire-options](leasing-get-failed-acquire-options.md) | bug | `leasing-get-failed-acquire-options` (af95e2ff8) | `leasing` (units 3–4) |
| [leasing-wait-rescind-no-delete](leasing-wait-rescind-no-delete.md) | bug | `leasing-wait-rescind-no-delete` (d3db62afd) | `leasing` (unit 5) |
| [leasing-stale-entry-after-reset](leasing-stale-entry-after-reset.md) | bug | `leasing-stale-entry-after-reset` (3d0769edc) | `leasing` (unit 5) |
| [leasing-update-stale](leasing-update-stale.md) | bug | `leasing-update-stale` (d97e455c2) | `leasing` (units 3–5) |
| [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md) | bug (fixed in the verified fork: `goose-lean` 0df483bee, unit W-Q) | `recipes-closed-watch-channel` (0aa6c6af8) | recipes, 2026-10-11 |
| [recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md) | bug (fixed in the verified fork: `goose-lean` 0df483bee, unit W-Q) | `recipes-closed-watch-channel` (0aa6c6af8) | recipes, 2026-10-11 |
| [recipes-pqueue-dequeue-order](recipes-pqueue-dequeue-order.md) | documentation | none | recipes (unit 2), 2026-10-11 |
| [raft-zero-max-size-per-msg](raft-zero-max-size-per-msg.md) | bug | none (etcd-io/raft; the format of the list above) | `raft` |
| [raft-memorystorage-createsnapshot-bounds](raft-memorystorage-createsnapshot-bounds.md) | documentation (an unstated range; below the compaction boundary a runtime panic, not `ErrCompacted`) | none (etcd-io/raft) | `raft` (`MemoryStorage`), 2026-10-12 |
| [raft-memorystorage-initialstate-unlocked](raft-memorystorage-initialstate-unlocked.md) | bug (a data race against the type's documentation) | none (etcd-io/raft) | `raft` (`MemoryStorage`), 2026-10-12 |
| [raft-config-clone-autoleave](raft-config-clone-autoleave.md) | bug (`Status().Config.AutoLeave` always false) | none (etcd-io/raft) | `confchange`, 2026-10-12 |
| [raft-changer-nil-incoming](raft-changer-nil-incoming.md) | undocumented precondition (panic) | none (etcd-io/raft) | `confchange`, 2026-10-12 |
| [raft-unknown-transition-panic](raft-unknown-transition-panic.md) | undocumented precondition (a committed entry panics every node, and again on every restart) | none (etcd-io/raft) | `raftpb` (`ConfChangeV2.EnterJoint`), 2026-10-13 |
| [raft-joint-empty-transition-panic](raft-joint-empty-transition-panic.md) | bug (an empty `ConfChangeV2` with a non-`Auto` transition is accepted while joint, committed, and panics every node; reproduced by a Go test) | `upamanyus/etcd-raft` `fix/raft-joint-empty-transition-panic` (9659828 test, e3f1575 fix, 4ea35f1 changelog, off 638f42739; pushed) | reconfiguration analysis (B1), 2026-10-14 |
| [raft-remove-last-voter-panic](raft-remove-last-voter-panic.md) | undocumented precondition (the leader accepts a conf change removing the last voter, which panics every node at apply; reproduced by a temporary Go test; in etcd only with `--strict-reconfig-check=false`, by code reading) | none (etcd-io/raft) | review of `fix/raft-joint-empty-transition-panic`, 2026-10-18 |
| [raft-prevote-stale-grant](raft-prevote-stale-grant.md) | bug (pre-vote's guarantee: a pre-candidate counts a grant from an earlier pre-campaign and raises its term; reproduced by Go tests) | none (etcd-io/raft) | pre-vote's term budget (`RawNode`), 2026-10-17 |
| [raft-readindex-singleton-stale](raft-readindex-singleton-stale.md) | bug (`ReadOnlySafe` read index answers stale reads at a single-voter configuration reached by a conf change: a new leader before its first commit, a removed leader; reproduced by a Go test; fixed in the fork commit `0560cb7` the proof pins, verified at `raft.Step` in both ghost modes, 2026-10-14) | `upamanyus/etcd-raft` `fix/raft-readindex-singleton-stale` (14d36dd test, b8a3280 fix, 3d0bd8a changelog, off 638f42739; the new-leader case since the split, 2026-10-18; pushed) | review of the reconfiguration paper proof, 2026-10-14 |
| [raft-readindex-removed-leader](raft-readindex-removed-leader.md) | bug (a leader that removed itself answers `ReadOnlySafe` read index requests at once with a stale index; reproduced by a Go test; split off `raft-readindex-singleton-stale`) | `upamanyus/etcd-raft` `fix/raft-readindex-removed-leader` (a15b631 test, 9fa83d5 fix, 30d3548 changelog, off 638f42739, pushed) | review of the reconfiguration paper proof, 2026-10-14; split 2026-10-18 |
| [raft-switchtoconfig-pending-reads](raft-switchtoconfig-pending-reads.md) | not a bug under `doc.go`'s protocol (postponed reads not released when a configuration change makes the leader's first commit; reachable only with `Advance` before `ApplyConfChange`; not filed) | none (etcd-io/raft) | code review of `fix/raft-readindex-singleton-stale`, 2026-10-18 |
| [raft-joint-self-quorum-read](raft-joint-self-quorum-read.md) | bug (liveness: a read at a leader that alone is a quorum of a joint configuration waits for heartbeat responses; reproduced by a temporary test) | fixed by the `fix/raft-readindex-removed-leader` candidate | code review of `fix/raft-readindex-singleton-stale`, 2026-10-18 |
| [raft-step-writes-caller-message](raft-step-writes-caller-message.md) | documentation (raft v3.7: `Step` writes into the caller's message and keeps it, `MemoryStorage.ApplySnapshot` fills its argument's nil fields, against `Step`'s "callers must treat m as immutable"; reproduced by a Go test) | none (etcd-io/raft) | the raft v3.7 retarget's inventory (R0), 2026-10-15 |
| [raft-confstate-unknown-fields-panic](raft-confstate-unknown-fields-panic.md) | bug (raft v3.7: a `ConfState` with an unknown field is "not equivalent" to the same configuration, so `newRaft` and snapshot restore panic; reproduced by a Go test) | `upamanyus/etcd-raft` `fix/raft-confstate-unknown-fields-panic` (b079b42 test, 71ca492 fix, 98c66a9 changelog, off 638f42739; pushed) | the raft v3.7 retarget (R1, the spec of `proto.Equal`), 2026-10-15 |
| [raft-joiner-empty-confstate](raft-joiner-empty-confstate.md) | undocumented precondition (with the initial `ConfState` in an index-0 snapshot, a node added later folds conf changes onto an empty configuration and wins alone; reproduced by a Go test) | none (etcd-io/raft) | review of the reconfiguration paper proof, 2026-10-14 |
| [raft-advance-before-applyconfchange](raft-advance-before-applyconfchange.md) | undocumented precondition (`Advance` before `ApplyConfChange`, which the docs allow, breaks state machine safety; reproduced by a Go test) | none (etcd-io/raft) | reconfiguration analysis (B0), 2026-10-13 |
| [raft-ready-messages-read-after-handout](raft-ready-messages-read-after-handout.md) | undocumented precondition (raft v3.7: `node.go`'s `acceptReady` reads the `To` of responses already handed out in `Ready.Messages`; not reproduced) | none (etcd-io/raft) | the raft v3.7 retarget (R5, the `Ready` predicates), 2026-10-16 |
| [raft-commit-lost-with-entries-kept](raft-commit-lost-with-entries-kept.md) | undocumented precondition (non-atomic persistence of entries and `HardState`; plausibility, abstract-model trace) | none (etcd-io/raft) | reconfiguration analysis (B0), 2026-10-13 |
| [raft-document-confchange-before-advance](raft-document-confchange-before-advance.md) | documentation (upstream draft for the two findings above: apply a `Ready`'s conf changes before `Advance`, persist entries and `HardState` atomically; also `ApplyConfChange`'s contradictory rejection rule) | none (etcd-io/raft) | reconfiguration analysis (B0), drafted 2026-10-14 |
| [raft-track-confchange-application](raft-track-confchange-application.md) | proposal (upstream draft: guards follow the conf changes passed to `ApplyConfChange`, opt-in; prototype with tests, `raft-conf-lag-model/guard-fix.patch`) | none (etcd-io/raft; the patch file) | reconfiguration analysis (parallel session), 2026-10-14 |
| [raft-snapshot-during-apply-stale-confchange](raft-snapshot-during-apply-stale-confchange.md) | bug (a snapshot restored while a `Ready`'s conf change is being applied: `ApplyConfChange` then applies it on top of the snapshot's configuration, a wrong configuration or a panic; reproduced by Go tests with hand-built leader messages) | `upamanyus/etcd-raft` `fix/raft-snapshot-during-apply-stale-confchange` (ca5cc04 test, 5b24f1e fix deferring the snapshot, da0e9bf changelog, off 638f42739, rebuilt 2026-10-18, pushed: the fork has c65d182b8; the guard-fix patch also fixes it) | guard fix (parallel session), 2026-10-14 |
| [raft-reportsnapshot-finish-not-noop](raft-reportsnapshot-finish-not-noop.md) | documentation the code contradicts (`Node.ReportSnapshot` says `SnapshotFinish` is a no-op; without it a leader can stay paused on a follower whose answer was lost; reproduced by a temporary Go test; etcd always reports it) | none (etcd-io/raft) | revising `raft-snapshot-during-apply-stale-confchange`, 2026-10-18 |
| [etcd-leader-advance-before-applyconfchange](etcd-leader-advance-before-applyconfchange.md) | possible bug, unconfirmed (the leader calls raft's `Advance` before applying a conf change, so raft accepts a concurrent membership change under the old configuration; ingredients confirmed by code reading and a raft Go test, not run on etcd) | none (fix proposed inline) | guard fix (parallel session), 2026-10-14 |
| [etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md) | bug (a committed entry panics every member, and again on every restart) | `txn-delete-then-ignore-put` (d9ba0e03c) | txn (unit 3), 2026-10-12 |
| [etcd-range-sort-none-limit](etcd-range-sort-none-limit.md) | bug | `fix/etcd-range-sort-none-limit` (1f10b22ed test, 6cb3f6108 fix, off 22cc5d9ac, pushed: replaces the pushed 972c22ce2; earlier draft `range-sort-none-limit` 7362d4129) | txn (unit 2), 2026-10-11 |
| [etcd-range-keys-only-lease](etcd-range-keys-only-lease.md) | bug (regression in v3.7, 7624a8a2e) | `range-keys-only-lease` (01e522548) | txn (unit 2), 2026-10-11 |
| [etcd-watch-sync-ticker-reset-zero](etcd-watch-sync-ticker-reset-zero.md) | bug (a panic on a coarse monotonic clock: Windows) | none | mvcc watchable store (unit 3b), 2026-10-12 |
| [etcd-apply-lease-checkpoint-sections](etcd-apply-lease-checkpoint-sections.md) | bug | `fix/etcd-apply-lease-checkpoint-sections` (9dc872522 test, 60d7c705e fix, off 22cc5d9ac; pushed; earlier draft `lease-checkpoint-one-section` 2a163496c) | apply (unit 1), 2026-10-12 |
| [etcd-watch-progress-interval-overflow](etcd-watch-progress-interval-overflow.md) | bug (a panic on a huge configured interval) | none (reproduced by an overlay test) | v3rpc watch (unit W-S), 2026-10-14 |
| [etcd-watch-id-reuse-stale-events](etcd-watch-id-reuse-stale-events.md) | bug (reproduced by an integration test, 2026-10-16) | `fix/etcd-watch-id-reuse-stale-events` (7a311ab5c test, 97aa6191d fix, off 22cc5d9ac; pushed) | v3rpc watch (unit W-S), 2026-10-14 |
| [etcd-watch-canceled-pending-retained](etcd-watch-canceled-pending-retained.md) | bug (minor: a canceled watcher's responses are kept for the stream's lifetime, up to 128 per cancel; from code reading) | none (fixed by the `etcd-watch-id-reuse-stale-events` candidate) | upstream report of `etcd-watch-id-reuse-stale-events`, 2026-10-16 |
| [etcd-stream-interceptor-err-before-done](etcd-stream-interceptor-err-before-done.md) | bug (a `context.Context` contract violation: `Err()` non-nil while `Done()` is open, in `Cancel`'s window; reproduced deterministically by an overlay test) | none | v3rpc stream interceptor (unit W-W), 2026-10-15 |
| [etcd-watch-resume-closing-substream](etcd-watch-resume-closing-substream.md) | bug (a client panic, "send on closed channel", after a transient stream failure; reproduced by an overlay test with a fake watch client) | none | client watch (unit W-C), 2026-10-15 |
| [etcd-watch-progress-before-created](etcd-watch-progress-before-created.md) | bug (a progress notification sent before a later watch's `Created` reaches the new watch, before its events; reproduced by an integration test) | none | client watch (unit W-K), 2026-10-16 |
| [etcd-watch-progress-closed-substream](etcd-watch-progress-closed-substream.md) | bug (a client panic, "send on closed channel", when a progress broadcast meets a server-canceled substream; reproduced by an overlay test with a fake watch client; fixed in the verified fork: `goose-lean` 107edf7e4, unit W-K) | `watch-progress-closed-substream` (57d502f38) | client watch (unit W-C), 2026-10-15 |

Findings without a draft yet (`notes/STATUS.md`, the leasing sections): `gatherOps` appending
into the caller's nested `OpTxn` slice (a race only for callers who reuse the slice; assessed,
not filed).
[etcd-txn-empty-requestop](etcd-txn-empty-requestop.md): the server's `txn.Txn` panics on a
`RequestOp` with an empty oneof, which the gRPC layer rejects (an unstated precondition; found
2026-10-11, txn unit 0; not filed).
[etcd-txn-nested-compare-snapshot](etcd-txn-nested-compare-snapshot.md): a nested transaction's
comparisons are evaluated before the outer transaction's operations run (undocumented; found
2026-10-12, txn unit 3; not filed).
[etcd-rangestream-sort-none](etcd-rangestream-sort-none.md): `RangeStream` accepts a sort by a
non-key target with `SortOrder: NONE` and returns duplicated and missing keys, since each chunk is
sorted by the target but the next chunk starts after the chunk's last key (a wrong result, outside
the verified code; found 2026-10-12 while fixing `etcd-range-sort-none-limit`; not filed; candidate and fork branch
`fix/etcd-rangestream-sort-none` (a8c642742 test, 638081c75 fix, off 22cc5d9ac; pushed 2026-10-19), 2026-10-18).
[etcd-apply-alarm-gauge-reactivate](etcd-apply-alarm-gauge-reactivate.md): the apply package's
alarm gauge counts an alarm activated twice twice (`AlarmStore.Activate` returns the existing
member) and stays at 1 after it is disarmed (a wrong metric; reproduced; found 2026-10-12, apply
unit 0; not filed).
[etcd-apply-authstatus-metric-label](etcd-apply-authstatus-metric-label.md): `dispatch` does not
set `op` for `AuthStatus`, whose apply latency is recorded under `op="unknown"` (a wrong metric
label; found 2026-10-12, apply unit 2; not filed).
[etcd-backend-duplicate-put-stale-read](etcd-backend-duplicate-put-stale-read.md): two puts of one
key in one batch session leave both in the backend's read buffer, and `ReadTx` returns the older
value (an unstated precondition of `UnsafePut`; reproduced; no etcd caller known to break it;
found 2026-10-12, backend unit 1; not filed).
[etcd-backend-read-buffer-cache-stale-after-commit](etcd-backend-read-buffer-cache-stale-after-commit.md):
`ConcurrentReadTx`'s buffer cache is keyed by a version a commit does not change, so after a
commit it can serve a deleted key (a reader in `Unlock`'s window) or an old value of a key the
pre-commit hook rewrote (deterministic); no wrong mvcc result known (reproduced twice; found
2026-10-12, backend unit 2; not filed; candidate and fork branch
`fix/etcd-backend-read-buffer-cache-stale-after-commit` (d426dcdb9 test, 1714a913c fix, off 22cc5d9ac; pushed), 2026-10-16).
[etcd-backend-put-value-too-large-fatal](etcd-backend-put-value-too-large-fatal.md): a put whose
encoded `KeyValue` exceeds bbolt's `MaxValueSize` (`2^31 - 2` bytes) makes the backend's
`unsafePut` call `lg.Fatal` (an unstated precondition of `UnsafePut`/`UnsafeSeqPut` and of mvcc's
`Put`; unreachable with the default request limit; found 2026-10-13, the backend bridge; not
filed).
[etcd-compaction-negative-batch-limit](etcd-compaction-negative-batch-limit.md): a negative
`CompactionBatchLimit` (an unvalidated flag; `NewStore` defaults only `0`) makes every compaction
job loop forever, force-committing every interval, its channel never closed (reproduced; found
2026-10-13, mvcc compaction unit 5a; not filed).
[etcd-compaction-delete-then-put](etcd-compaction-delete-then-put.md): compacting at a revision
that deletes a key and puts it again deletes the key's live value from the bucket, and the next
read of the key calls `lg.Fatal` (reproduced through mvcc's API, and on 2026-10-14 through the
gRPC API with a from-key delete, which `checkIntervals` does not see as overlapping the put
(`etcd-txn-delete-then-ignore-put`): the member exits on the read and, restarted, has lost the
acknowledged value; found 2026-10-13, mvcc compaction unit 5a; not filed).
[etcd-index-compact-overlapping](etcd-index-compact-overlapping.md): two overlapping
`treeIndex.Compact` passes can compact a key index the other deleted (`lg.Panic`) or delete a key
put again in between (an unstated precondition of the `index` interface; unreachable through the
store, whose FIFO scheduler runs the jobs one at a time; reproduced; found 2026-10-13, mvcc
compaction unit 5b; not filed).
[etcd-request-id-member-prefix](etcd-request-id-member-prefix.md): request ids are unique per
member's low 16 bits only (`idutil.NewGenerator(uint16(memberID), …)`), so two members whose ids
agree there can mint the same request id, and one member's apply thread can hand another's
request result to its own waiter (reproduced; found 2026-10-12, the request path's unit 0; a
premise of the raft contract's apply side; not filed).
[etcd-max-txn-ops-nested](etcd-max-txn-ops-nested.md): `--max-txn-ops` bounds each nesting level
of a transaction, not the transaction (the flag's text says a transaction; reproduced; found
2026-10-12, the request path's unit 0; documentation; not filed).
[etcd-txn-check-intervals-sibling](etcd-txn-check-intervals-sibling.md): `checkIntervals` checks a
nested transaction's puts against the level's deletes collected so far, not its siblings', so the
overlap it rejects depends on the order of the ops (reproduced; found 2026-10-12, the request
path's unit 0; not filed).
[etcd-client-retry-put-ctx-error](etcd-client-retry-put-ctx-error.md): the client's retry
interceptor retries any unary call, a `Put`'s included, after an attempt fails with a gRPC
`Canceled` or `DeadlineExceeded` while the caller's context is live (a branch for a per-attempt
context etcd no longer has), bypassing `isSafeRetryMutableRPC`'s write-at-most-once: a write the
first attempt applied is applied again (reproduced with a mock server; found 2026-10-14, unit C1,
the client meets the server; not filed).

[etcd-auth-token-md-empty](etcd-auth-token-md-empty.md): the auth store's `AuthInfoFromCtx`
indexes `ts[0]` of the token key's metadata values unchecked: a panic on an incoming context whose
metadata has the key with no value (only an in-process caller can build one; reproduced; found
2026-10-14, unit P2, the auth store's request side; not filed).
[etcd-auth-tls-info-assert](etcd-auth-tls-info-assert.md): `AuthInfoFromTLS` asserts the peer's
`AuthInfo` is a `credentials.TLSInfo` (one-result form): a panic for a peer with other
credentials, an unstated precondition (unreachable in etcd's servers; reproduced; found
2026-10-14, unit P2; not filed).
[go-itab-reinterpret-assert](go-itab-reinterpret-assert.md): in Go itself, a type assertion
on an `I1` value read through a `*I2` (two named interfaces with the same methods) panics with
"main.I2 is main.T, not main.T", and `==` with an `I2` holding the same value is false, since the
compiler compares itabs (found 2026-10-13, Perennial's byte-memory review, round 3; the golang/go
issue drafted in `upstream/go-itab-reinterpret-assert/`, not filed).
Leads not yet assessed: the gRPC proxy's cache (`server/proxy/grpcproxy/cache/store.go`) builds
its intervals as `checkIntervals` did, so a cached from-key range may never be invalidated.

## bbolt

Found by the bbolt proof (branch `bbolt`, not merged: bbolt v1.5.0 on Perennial's provisional
unsafe-memory model; `notes/STATUS.md` there, "bbolt"), each reproduced by a Go test kept next to
it (copy it into bbolt's package directory) unless said otherwise; none filed:
[bbolt-commit-meta-error-frees-reader-pages](bbolt-commit-meta-error-frees-reader-pages.md)
(a `Commit` whose meta write reaches the file and then fails rolls back by reloading the new
freelist: pages an open reader still reads are reused, its snapshot changes; and the "failed"
commit takes effect), [bbolt-max-value-size-unusable](bbolt-max-value-size-unusable.md) (a value
of `MaxValueSize` panics `Commit`; a leaf of a few values near it commits and then panics every
read), [bbolt-large-page-size](bbolt-large-page-size.md) (`Options.PageSize` unbounded: from
about 1 MiB a 65535-entry leaf panics `Commit`, from `2^31` the first `Commit` panics, from
`2^32` the meta stores it truncated), [bbolt-mmap-madvise-leak](bbolt-mmap-madvise-leak.md) (a
failed `madvise` leaks the new mapping; code reading). Checked and not real at v1.5.0 (so not
here): a nil `db.data` after a failed remap (`Begin` checks it, `ErrInvalidMapping`), a forged
meta found by `getPageSize`'s probes (they stay inside page 0, zero after the meta),
`hashMap.Init([])`'s stale cache (no caller reaches it with stale free ids), panics on a
malformed file (bbolt trusts its file).
