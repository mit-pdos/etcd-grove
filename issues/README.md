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
| [raft-memorystorage-createsnapshot-bounds](raft-memorystorage-createsnapshot-bounds.md) | documentation (an unstated range; below the compaction boundary a runtime panic, not `ErrCompacted`) | none (etcd-io/raft) | `raft` (`MemoryStorage`), 2026-10-12 |
| [raft-memorystorage-initialstate-unlocked](raft-memorystorage-initialstate-unlocked.md) | bug (a data race against the type's documentation) | none (etcd-io/raft) | `raft` (`MemoryStorage`), 2026-10-12 |
| [etcd-txn-delete-then-ignore-put](etcd-txn-delete-then-ignore-put.md) | bug (a committed entry panics every member, and again on every restart) | `txn-delete-then-ignore-put` (d9ba0e03c) | txn (unit 3), 2026-10-12 |
| [etcd-range-sort-none-limit](etcd-range-sort-none-limit.md) | bug | `range-sort-none-limit` (7362d4129) | txn (unit 2), 2026-10-11 |
| [etcd-range-keys-only-lease](etcd-range-keys-only-lease.md) | bug (regression in v3.7, 7624a8a2e) | `range-keys-only-lease` (01e522548) | txn (unit 2), 2026-10-11 |

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
Leads not yet assessed: the gRPC proxy's cache (`server/proxy/grpcproxy/cache/store.go`) builds
its intervals as `checkIntervals` did, so a cached from-key range may never be invalidated.
