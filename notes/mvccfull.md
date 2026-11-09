# mvccfull: a tester of all of mvcc that etcd uses, for a proof that it never fails

Branch `worktree-mvcc-full-tester`, 2026-11-09. The user asked for a better mvcc test than
`examples/mvccrand` (`notes/mvccrand.md`): not to search for bugs, but to cover, in principle,
**all** the important executions of mvcc, so that knowing the test never fails gives confidence
in mvcc's correctness. Then (mid-session): keep the core easy to audit. What only makes
interesting executions likely goes in a configuration, the theorem is for all configurations, and
the Go tests run engineered configurations. No proof yet.

## What mvccrand left out (the review that started this)

mvccrand covers the part of mvcc that etcd's current proof relies on: one writer with txn-style
transactions, floored concurrent reads, one watch stream, lease attach and detach. It leaves out
much of what etcd's *code* relies on:

- compaction (it asserts `CompactRevision == 0`);
- restart and recovery from the file;
- `Restore` (snapshot install);
- hashing (the corruption checker);
- watch from revision 0, `Cancel`, filters, the previous key-value read, explicit ids;
- more than one stream;
- liveness: its `Main` checks only what arrived, so a store that sent no event would pass.

Its choices come from a seeded generator, and its closed theorem is about one seed.

## The tester (`examples/mvccfull`)

- `mvccfull.go` is the core, with the checks.
- `config.go` holds `Config` and `Mix`: sizes, mvcc's batch settings, weights, sleeps.
- `mvccfull_test.go` holds the engineered configurations.

The package doc comment (`mvccfull.go`) is the specification. In short:

- **Choices**: every choice is `primitive.RandomUint64` (random in Go, any value in GooseLang)
  through `choose`/`pick`. A theorem "`Run(cfg)` never panics, for every `cfg`" therefore
  quantifies over every choice sequence, interleaving and configuration.
- **Configuration**: every `Config` is valid; `normalize` clamps out-of-range values. A `Mix`
  only reweighs alternatives, all of which stay possible: an absent or zero weight still allows
  its alternative when every weight is 0, since the choice is then uniform. Sleeps are no-ops
  in the model. So `config.go` cannot weaken a check; the auditor of the checks can skip it.
- **The system**: two members as the server sets one up (backend, real lessor, `mvcc.New`, the
  post-lock hook after the store), one operation log, a leader and a lagging follower.
  - The writer is the only goroutine that writes, commits, compacts, restores or restarts, like
    etcd's apply loop (the precondition of `nonissues/etcd-mvcc-progress-lock-order-deadlock.md`).
  - Its operations: Put, DeleteRange, Txn (the three ways `txn.Txn` reads its compare), lease
    grant/revoke/put-with-lease, Compact at any revision (waiting or not), Commit.
  - Member steps: the follower applies some of the log; the follower installs the leader's
    snapshot (the server's `applySnapshot`: file, `backend.New`, `Lessor.Recover`, `Restore`,
    hook, old backend closed); a member restarts cleanly (streams drained and closed, everything
    closed and reopened on the file).
- **Readers** run on each member: Rev, FirstRev, read and read-only transactions, the store's own
  Range, and the corruption checker:
  - `HashByRev` on both members, equal when the revision and compaction revision are equal;
  - each member's compaction hashes against the other's `HashByRev` of their revision, as
    `CompactHashCheck` compares them.
- **Watch streams** on each member:
  - registrations from 0 or any revision, any range, the NoPut/NoDelete filters, automatic and
    explicit ids;
  - cancels, `RequestProgress`, `RequestProgressAll`, the stream's `Rev`;
  - the calls that must fail;
  - the watch server's previous key-value read on received events.
- **The oracle**: the leader appends each revision to a shared history before its `End`. Where
  concurrency makes a value unknowable, it is checked against bounds published before and after
  each step (`revLo/revHi`, `cmpLo/cmpHi`). A read transaction's `FirstRev` is exact for its
  ranges (`store.mu` is held across it).
  - A watcher from 0 starts somewhere in a window until its first event anchors it.
  - A stream progress response (id -1) is checked for the watchers in every `RequestProgressAll`
    set not yet answered. A response can be dropped when the channel is full, so this is sound.
- **Liveness, as partial correctness can state it**: before a stream is closed (at a restart and
  at the end), the writer waits until every watcher not cancelled or compacted has every change
  up to the member's revision. So `Run` returns only if nothing was lost. At the end both
  members restart once more and every uncompacted revision is read in full.

### Restrictions (each a known bug; lifted when it is fixed)

| restriction | issue |
|---|---|
| no `Compact(0)` | `issues/etcd-mvcc-hashbyrev-zero-stored.md`, `issues/etcd-restore-scheduled-compact-zero.md` |
| < 512 watchers per member | `issues/etcd-watch-compacted-resent.md` |
| explicit watch ids never reused | `issues/etcd-watch-id-reuse-stale-events.md` |
| no full-store `Hash()` | `issues/etcd-mvcc-hash-currentrev-race.md` (fixed upstream after the pin) |
| stored-hash path's current revision unchecked | `issues/etcd-mvcc-hashbyrev-restore-rev1.md` |
| the writer waits for a compaction only before its next step | `issues/etcd-restore-pending-compaction-unclosed.md` |
| hashes of an empty keyspace need not agree | `issues/etcd-mvcc-compact-hash-empty-keyspace.md`, `issues/etcd-mvcc-hashkv-during-compaction-empty-keyspace.md` (new, below) |
| no negative compaction batch limit | `nonissues/etcd-compaction-negative-batch-limit.md` |
| a txn's puts distinct and outside its deletes | etcd's `checkIntervals` (`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`) |

### Not covered

- **Crashes.** Restarts are clean. Two injected bugs (M1, M7 below) differ from mvcc only after a
  crash. Covering crashes needs Perennial's crash semantics and a model of the backend file's
  crash states.
- **More than 10000 distinct keys** (`restoreChunkKeys`'s key-index cache eviction): a `Depth ≥ 9`
  configuration has them, `MainConfig` (`Depth 4`, 120 keys) does not.
- **Termination.** Liveness is checked only as "if `Run` returns".
- **The lessor's own behavior** (expiry, checkpoints, promotion): the lessor is never promoted.
- **Several writers on a store**: etcd has one.
- **Older snapshots**: restoring one panics in etcd itself.
- **Defragmentation**: the backend's, not mvcc's.
- **Under `maxWatchersPerSync`**: the > 512-watcher path is excluded (restriction above).

## Found: a false corruption alarm (2 issues)

The cross-member hash check failed with three keys (`fewKeys`). `kvHasher` skips old entries only
when `keep` is non-empty. `HashByRev`'s `keep` (`kvindex.Keep(rev)`) is empty exactly when no
key is live at `rev`, and the compaction's `keep` (`kvindex.Compact`) differs from it (it holds a
tombstone at the revision).

- **`issues/etcd-mvcc-compact-hash-empty-keyspace.md`** (`upstream: none`): a follower that has
  not yet applied a compaction gives a different hash than the leader's stored compaction hash at
  the same revision and compaction revision. `CompactHashCheck` (alpha feature gate) raises a
  CORRUPT alarm, and every member then rejects reads and writes. etcd-io/etcd#22515 does not fix
  it.
- **`issues/etcd-mvcc-hashkv-during-compaction-empty-keyspace.md`** (`upstream: known`,
  etcd-io/etcd#22517 and #22515): the hash depends on a running compaction's progress.

Both fail 20 of 20 at etcd-io/etcd@d622ec57 (2026-11-06).

## Does it have teeth (mutation testing, 2026-11-09)

Bugs injected one at a time into a copy of the pinned server module (`go test -modfile` with a
replace), each run against `TestRun`'s engineered configurations:

| mutation | result |
|---|---|
| M2 restart: keys' leases not re-attached | fail (lessor check) |
| M3 compaction drops the tombstone at the compaction revision | hang (a watcher from the compaction revision never gets the delete: the end-of-epoch drain) |
| M4 a read at exactly the compaction revision fails | fail |
| M5 a watcher one below the compaction revision not compacted | hang (its lost events are its last) |
| M6 an unsynced victim's next revision off by one | fail (`slowReceiver` only) |
| M8 an interrupted compaction not resumed at restart | fail |
| M11 a re-compaction at the same revision accepted | fail |
| M12 a victim's response revision below its events' | fail |
| M15 watch filters inverted | fail (`slowReceiver`) |
| M16 progress before a watcher's start revision | fail |
| M1, M7 the revision restored below the compaction revision / the scheduled one | pass: equivalent without crashes |
| M9 the finished-compaction record not written | pass: only stops a compaction hash from being stored after a restart |

Before the engineered configurations, M3 and M6 passed: they need a watcher from exactly the
compaction revision, and a full channel during a sync. That is the reason for the `Mix` weights
(`compactionEdge`, `slowReceiver`). "A hang" means `go test`'s timeout; a theorem of partial
correctness says nothing about it.

## Runs

`go test -race -short ./mvccfull/` (from `examples/`): 18 runs over 5 configurations, about 2
minutes, pass. `TestMain_` (`MainConfig`: 12000 operations, 120 keys, values up to 5000 bytes):
about 7 s; for example 5021 revisions, 6426 events, 1623 compaction responses, 81 snapshot
installs, 86 restarts, 44485 hash pairs compared.

## For a proof

- Translated: `etc/goose.py` project `mvccfull`, `Code/.../examples/mvccfull.lean`. Both
  generated files elaborate against `lean`'s build.
- The theorem to aim for is `Run.spec` for every `Config`.
- The closed theorem: `Main` (`MainConfig`) like `mvccrand_adequate`, with the files absent at
  start (`dbFilesAbsent` of every path a run may create: `Prefix-<member>-<gen>.db`, unbounded
  generations, so a premise over a prefix rather than a list).
- Specs it needs beyond mvccrand's:
  - mvcc: `Compact` (today only over mvcc's assumed backend: `notes/mvccrand.md`, first version,
    (1)-(2)), `Restore`, `HashByRev`/`Hashes` (out of the API, `Api.lean`), the store's own
    `Range`, `FirstRev`, `Cancel`, filters;
  - the backend: `Snapshot().WriteTo` a file and `backend.New` on it;
  - the lessor: `Recover`, `Leases`, `Lookup`/`Keys` after a restart;
  - `os.Create`;
  - `primitive.RandomUint64` (Perennial has it).
- The watch oracle's invariants (the anchoring window, the `allQ` intersection) are the delicate
  part. They are written to be stated as invariants of the stream's lock.
