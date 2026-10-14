# Issues found while verifying

One file per issue found in the verified Go code (raft, etcd, their dependencies) or its
documentation: a bug (a reachable panic or wrong result), a precondition the code needs
but its API does not state, or documentation the code contradicts. Not for bugs in this
repository's own specs and proofs (those go in `notes/`).

Name a file `<project>-<short-slug>.md` and give it:

- **Status**: open / reported (link) / fixed upstream (commit) / not a bug (why).
- **Where**: the Go code (file:line at the pinned revision in `etc/goose.py`) and the
  documentation involved.
- **What happens**: the behavior, with a reproduction (a Go test, inline or by path) when
  one exists.
- **Expected**: what the documentation or API promises instead.
- **How the proof handles it**: the premise, spec or scope choice that keeps it out of the
  verified results (file:line).
- **Possible fixes**.
- **Found**: date and by what (which proof or check).

## Drafts for etcd-io/etcd

The findings of the etcd client-side work (cache, concurrency, leasing, recipes) are written as
drafts of the issues to file against etcd-io/etcd, one per finding (the proofs state what the
code does; a finding is a behaviour the specs could not hide): each names the upstream revision
it refers to, how to reproduce it (a test on the fix branch) and the fix. The fix branches are
on the fork `upamanyus/etcd`, one signed-off commit each off upstream `main` (f061acd09), with
the tests; the issues and pull requests are filed by hand from them. A finding that is not a bug
(a documentation request) has no fix branch. A draft covers the fields above in its own order
(summary, what happens, how to reproduce, expected, the fix); "How the proof handles it" is in
`notes/STATUS.md`'s section for the package.

| Draft | Kind | Fork branch | Found in |
|---|---|---|---|
| [cache-ready-after-retry](cache-ready-after-retry.md) | bug | `cache-ready-after-retry` (64313a1f8) | `cache` (STATUS "The whole package") |
| [mutex-lock-recreated](mutex-lock-recreated.md) | bug | `mutex-lock-recreated` (113b0b324) | `concurrency` (Mutex) |
| [election-campaign-key-check](election-campaign-key-check.md) | bug | `election-campaign-key-check` (bb50d33b8) | `concurrency` (Election) |
| [stm-serializable-snapshot](stm-serializable-snapshot.md) | documentation | none (`stm-serializable-snapshot` kept local, not proposed) | `concurrency` (STM) |
| [leasing-evictrange-key](leasing-evictrange-key.md) | bug | `leasing-evictrange-key` (14d1c4bf3) | `leasing` (units 1–2) |
| [leasing-evalcmp-missing-key](leasing-evalcmp-missing-key.md) | bug | `leasing-evalcmp-missing-key` (06541aec6) | `leasing` (units 1–2) |
| [leasing-modify-uncached-once](leasing-modify-uncached-once.md) | bug | `leasing-modify-uncached-once` (7a6077dec) | `leasing` (units 3–4) |
| [leasing-get-failed-acquire-options](leasing-get-failed-acquire-options.md) | bug | `leasing-get-failed-acquire-options` (af95e2ff8) | `leasing` (units 3–4) |
| [leasing-wait-rescind-no-delete](leasing-wait-rescind-no-delete.md) | bug | `leasing-wait-rescind-no-delete` (d3db62afd) | `leasing` (unit 5) |
| [leasing-stale-entry-after-reset](leasing-stale-entry-after-reset.md) | bug | `leasing-stale-entry-after-reset` (3d0769edc) | `leasing` (unit 5) |
| [leasing-update-stale](leasing-update-stale.md) | bug | `leasing-update-stale` (d97e455c2) | `leasing` (units 3–5) |
| [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md) | bug | `recipes-closed-watch-channel` (0aa6c6af8) | recipes, 2026-10-11 |
| [recipes-barrier-wait-closed-watch](recipes-barrier-wait-closed-watch.md) | bug | `recipes-closed-watch-channel` (0aa6c6af8) | recipes, 2026-10-11 |
| [recipes-pqueue-dequeue-order](recipes-pqueue-dequeue-order.md) | documentation | none | recipes (unit 2), 2026-10-11 |
| [raft-zero-max-size-per-msg](raft-zero-max-size-per-msg.md) | bug | none (etcd-io/raft; the format of the list above) | `raft` |
| [etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md) | bug (a committed entry panics every member, and again on every restart) | `txn-delete-then-ignore-put` (d9ba0e03c) | txn (unit 3), 2026-10-12 |
| [etcd-range-sort-none-limit](etcd-range-sort-none-limit.md) | bug | `range-sort-none-limit` (7362d4129) | txn (unit 2), 2026-10-11 |
| [etcd-range-keys-only-lease](etcd-range-keys-only-lease.md) | bug (regression in v3.7, 7624a8a2e) | `range-keys-only-lease` (01e522548) | txn (unit 2), 2026-10-11 |
| [etcd-watch-sync-ticker-reset-zero](etcd-watch-sync-ticker-reset-zero.md) | bug (a panic on a coarse monotonic clock: Windows) | none | mvcc watchable store (unit 3b), 2026-10-12 |
| [etcd-apply-lease-checkpoint-sections](etcd-apply-lease-checkpoint-sections.md) | bug | `lease-checkpoint-one-section` (2a163496c) | apply (unit 1), 2026-10-12 |

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
the verified code; found 2026-10-12 while fixing `etcd-range-sort-none-limit`; not filed).
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
2026-10-12, backend unit 2; not filed).
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
read of the key calls `lg.Fatal` (reproduced through mvcc's API; etcd's gRPC `checkIntervals`
rejects such a transaction; found 2026-10-13, mvcc compaction unit 5a; not filed).
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

[go-itab-reinterpret-assert](go-itab-reinterpret-assert.md): in Go itself, a type assertion
on an `I1` value read through a `*I2` (two named interfaces with the same methods) panics with
"main.I2 is main.T, not main.T", since the runtime compares itabs (found 2026-10-13, Perennial's
byte-memory review, round 3; unclear what in Go should change; not filed).
Leads not yet assessed: the gRPC proxy's cache (`server/proxy/grpcproxy/cache/store.go`) builds
its intervals as `checkIntervals` did, so a cached from-key range may never be invalidated.
