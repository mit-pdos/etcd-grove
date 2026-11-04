# mvccmodel: a randomized model test of etcd's mvcc store

`examples/etcd/mvccmodel` (branch `mvcc-model-test`, 2026-11-04). The user's request: a new
top-level test of mvcc, separate from `examples/etcd/mvccrand` (branch `mvcc-api`, which another
session is proving), as simple to audit as possible, and permitting every execution mvcc's users
care about: totally random operations run concurrently over all of mvcc's public API. Not forcing
interesting interleavings: it is enough that they are possible. The aim is a test good enough to
check a reimplementation of mvcc (other data structures), and to propose upstream.

Not translated (no Goose configuration); a test only, `go test ./etcd/mvccmodel/` from `examples/`
(about a second per seed; `-mvccmodel.seeds=N -mvccmodel.seed=S`).

## How it works

- **Goroutines.** One *applier* makes every change, as etcd's apply loop does: write transactions
  (Put, DeleteRange, Range, Rev, FirstRev, Changes), the store's own Put and DeleteRange, Compact,
  Commit, Restore (from its own backend), `HashStorage().Hash`, lease Grant and Revoke (the lessor
  deletes the lease's keys through mvcc), puts with leases, the lessor's view of the keys' leases,
  read transactions. *Readers*: read transactions in both modes (some through
  `NewReadOnlyTxnWrite`), the store's Range, Rev and FirstRev, `HashByRev`, `Hashes`. *Watch-stream
  owners*: Watch (auto, explicit and duplicate IDs, empty ranges, start 0, past and future
  starts, put/delete filters), Cancel (live or not), RequestProgress, RequestProgressAll, Rev,
  Close then a new stream; each stream's Chan drained by its own goroutine. The readers and owners
  run until the applier's operations are done. Every choice is uniformly random.
- **Recording.** A shared logical clock stamps each call before it starts and after it returns.
  Each goroutine records its calls with their results; nothing is checked while it runs.
- **The model** (in the same file, beside the calls): the key-values at each revision, the changes
  making each revision, the successful compactions. The applier's log, replayed in order, builds it
  and checks each applier operation against it (its results, Changes, the revisions it reports).
- **Concurrent observations.** A step that changes what a reader can see (revision, compaction
  revision) starts an *epoch*. An observation made during `[a, b]` must agree with the model at an
  epoch that may have been current then: begun before `b`, not replaced before `a`. A read
  transaction must agree in its Rev, FirstRev and every range; no search is needed (the applier
  is sequential, so the epochs are totally ordered).
- **Watches.** Per stream, the owner's calls are checked in order (auto IDs, duplicate and empty
  range errors, Cancel's errors, RequestProgressAll with no watchers returning true), then the
  responses in delivery order: each watcher's events are the model's changes in its range from its
  start revision, in order, all fields (a start of 0 may be any revision the store had during the
  Watch call, narrowed by what arrives); a response holds all of a revision's events and its
  revision is at least theirs; a progress response (one watcher's, or the stream's, matched to the
  RequestProgressAll call that returned true) comes after every change at or below its revision; a
  compaction response names a successful compaction above the watcher's next revision, and nothing
  follows it. At the end, every live watcher must receive every change it watches.
- **Hashes.** `HashByRev` is computed from the model, as mvcc's `kvHasher` hashes the key bucket
  (bucket keys, marshaled key-values, the keep set, the tombstone at the compaction revision); so is
  each compaction's stored hash, which `HashByRev` returns for its revision and `Hashes` lists.
- **At the end.** Compactions after the last Restore must finish (their channels close). The store,
  quiescent, then again after a restart (closed, then `mvcc.New` with a new lessor over the same
  backend): Rev, FirstRev, every revision from the compaction on read in full and hashed, every
  key's lease.

## Restrictions, and why

Each leaves out an execution etcd does not produce, or one a recorded finding already covers:

- **One writer.** Every change (writes, Compact, Commit, Restore, revokes) is the applier's. With two
  goroutines changing the store, a progress request can deadlock
  (`nonissues/etcd-mvcc-progress-lock-order-deadlock.md`, branch `mvcc-api`); etcd applies on one
  goroutine. `Hash` runs there too: its documentation excludes ongoing transactions (and at the pin it
  reads the revision without a lock, `issues/etcd-mvcc-hash-currentrev-race.md`, `mvcc-api`).
- **A revision changes a key at most once** (no put of a key a transaction already changed, no
  range delete over one): etcd's gRPC layer rejects such a txn; with one, a watch from the
  compaction revision loses events (`nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md`,
  `mvcc-api`).
- **No `Compact(0)`** (`issues/etcd-mvcc-hashbyrev-zero-stored.md`, `mvcc-api`;
  `nonissues/etcd-restore-scheduled-compact-zero.md`), **no negative revisions** (rejected by the
  gRPC layer; `nonissues/etcd-mvcc-watch-negative-start-rev.md`, `mvcc-api`).
- **No watch ID is used twice on a stream** (a canceled watch's queued responses cannot be told apart
  from the new watch's: `issues/etcd-watch-id-reuse-stale-events.md`).
- **`HashStorage.Store` is not called** (only mvcc's compaction calls it).

Tolerated deviations, each narrow and pointing at its finding:

- `TxnWrite.FirstRev` is 0 (not the documented compaction revision): either is accepted
  (`nonissues/etcd-mvcc-txnwrite-firstrev-zero.md`).
- During a Restore, `HashByRev` of a stored hash's revision reports current revision 1
  (`issues/etcd-mvcc-hashbyrev-restore-rev1.md`, `mvcc-api`): accepted while a Restore runs (a
  "restoring" epoch). The test found it on its own (seed 106 under `-race`).
- A compaction's done channel need not close if a Restore came after it
  (`issues/etcd-restore-pending-compaction-unclosed.md`).
- **HashByRev of an empty key space.** When no key is live at the hashed revision, mvcc's hasher has
  an empty keep set and hashes every revision up to the compaction revision still in the backend:
  the value depends on how far the asynchronous compaction has got. Found by this test (seed 2: a
  compaction at 6, where revision 6 deleted every key; `HashByRev(6)` hashed every revision up to 6
  until the compaction job ran). Its revisions are checked, not its value; the finding is recorded
  in `issues/` or `nonissues/` (`etcd-mvcc-hashbyrev-empty-keyspace-*`).
- `Hash`'s value is not checked (the whole backend: lease and meta buckets, revisions a compaction
  has not yet deleted), only its revision.

## What it reaches (2026-11-04)

- `go test -race`, seeds 1-20 and 100-199: pass (after the deviations above).
- Statement coverage of `storage/mvcc` over 20 seeds: 81%. Not reached: the slow-watcher (victim)
  path (a full 128-response channel: possible, as a receiver can be descheduled, but not seen; the
  receivers only append), more than 512 unsynced watchers at once (`choose`'s other branch: the scale
  is too small), more than 10000 keys in a restore chunk, catch-ups of more than 1000 revisions
  (`watchBatchMaxRevs`) rarely, metrics, the panics.
- **Mutations** (one at a time, in a copy of the pinned module, `-modfile`; 5 seeds each): caught:
  a read at the compaction revision failing; a limited range's count ignoring `WithTotalCount`; a
  catch-up skipping the event at `minRev`; progress sent to a watcher whose start is ahead; a restart
  losing the keys' leases; a recreated key's version off by one. Not caught, and not observable
  within the restrictions: a txn's DeleteRange not seeing the txn's own puts (needs a key changed
  twice in a revision); `keep` keeping the tombstone at its revision (changes only the empty key
  space's hash, which is not checked).

## Next

- Upstream: port it into `server/storage/mvcc` as a `_test.go` (etcd's test helpers; the restriction
  list as the precondition etcd's callers meet), after the findings it relies on are settled.
- A reimplementation of mvcc is checked by pointing the examples module's `replace` (or `-modfile`)
  at it.
