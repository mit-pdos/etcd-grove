# Plan: prove `store.restore` and close `store.Restore`

Status: R0 done (2026-10-23, branch `restore-r0`); R1-R6 to do. Removes two of mvcc's trust-boundary axioms,
`mvcc.store.restore.wp_proof` and `mvcc.store.Restore.wp_proof` (539 to 537), both on the snapshot
receiver's path (D22: `applySnapshot` → `watchableStore.Restore` → `store.Restore` → `restore`) and
`restore` on every boot (`NewStore`). Follows the spec check of 2026-10-23 (`notes/STATUS.md`): both
specs agree with the code at the etcd pin (`188113160`), with one gap (below, R2).

## Goal

`store.restore` and `store.Restore` theorems over their translated bodies, under the premises their
specs have today: no compaction recorded in the backend (`kbNoCmp`; for `Restore` also `crevFrozen`),
no lease in the restored log and every revision with a change (`restoreLogOk`). No closed theorem's
statement changes (fingerprint), the trust base loses the two axioms and gains none.

Out of scope, a later plan: restoring a compacted store (the finished and scheduled compaction
paths, resuming a compaction through `compactLockfree`) and leases (`le.Attach` per key). Both stay
excluded by the premises, so the server's workloads (no compaction, no leases) are what the proofs
cover, as today.

## The code (`server/storage/mvcc`, at the pin)

- `store.Restore(b)` (`kvstore.go:292`, translated): under `s.mu`, closes `s.stopc`, stops the old
  scheduler, installs `b` and `newTreeIndex(s.lg)`, resets `currentRev = 1`, `compactMainRev = -1`
  under `s.revMu`, makes a new scheduler and stop channel, calls `s.restore()`.
- `store.restore()` (names-only): `setupMetricsReporter()`; reads the finished and scheduled
  compaction keys; starts `restoreIntoIndex`; reads the `Key` bucket in chunks of
  `restoreChunkKeys` (`tx.UnsafeRange(Key, min, max, limit)`, the next `min` one past the last key's
  revision), each chunk through `restoreChunk`; closes the channel and takes `currentRev` from
  `revc` (raised to the compaction revisions if lower); attaches `keyToLease`; resumes a scheduled
  compaction.
- `restoreIntoIndex(lg, idx)` (names-only): makes a buffered channel `rkvc` (capacity
  `restoreChunkKeys`) and `revc` (capacity 1), starts a goroutine that receives every
  `revKeyValue`, keeps a cache `kiCache` of key indexes (purging 10 entries by a map range with
  `delete` when full), finds or creates the key's `keyIndex` (`idx.KeyIndex`, `ki.restore`,
  `ki.restoreTombstone`, `idx.Insert`), applies the revision (`ki.put`, `ki.tombstone`), checks
  revisions do not decrease (`verify.Verify`), and finally sends the last revision on `revc`.
- `restoreChunk(lg, kvc, keys, vals, keyToLease)` (names-only): unmarshals each value
  (`proto.Unmarshal` into `mvccpb.KeyValue`), updates `keyToLease`, sends on `kvc`.
- `keyIndex.restore`, `keyIndex.restoreTombstone` (names-only), `setupMetricsReporter`
  (names-only): five package closures under five package mutexes.

## Stages

**R0. Translate. Done (2026-10-23).** `store.restore`, `store.setupMetricsReporter`,
`restoreIntoIndex`, `restoreChunk`, `keyIndex.restore`, `keyIndex.restoreTombstone` and the variable
`restoreChunkKeys` translated (`mvcc.toml`); Goose took all of them as they are (the goroutine's
`defer`, the channel range as `chan.forRange`, the map range with `delete`), no fork change. The
type `revKeyValue` was already translated (`translate_types`). `restoreChunkKeys`'s initializer is
translated, so the generated opaque-initializer axiom `restoreChunkKeys.init` is gone and `mvccInit`
states its value (`globalAddr restoreChunkKeys ↦□ (W64 10000 : w64)`, appended last; `gen-init.py`:
its allocation type, the `before` steps re-anchored on `defaultCompactionBatchLimit`, `apply`'s
pattern of `mvccInit` one conjunct longer). The two axioms still state their specs, now over
translated bodies. The plan as written: Add to `Code/go_etcd_io/etcd/server/v3/storage/mvcc.toml`: `store.restore`,
`store.setupMetricsReporter`, `restoreIntoIndex`, `restoreChunk`, `keyIndex.restore`,
`keyIndex.restoreTombstone` (and the type `revKeyValue` if names-only). `etc/goose.py --project
etcd`; the translation must build. Check what Goose makes of the goroutine with `defer` and the
`range` over a channel; a map range with `delete` is in Perennial's model (`wp_map_for_range_mut`).
`restoreChunkKeys` is a package variable with an opaque initializer (`opaqueInitsOk`): `make` of a
channel of negative capacity panics, so the proof needs its value non-negative; translate its
initializer (`= 10000`, a literal) through `etc/gen-init.py`'s `SPECIAL` for mvcc, or state the
fact there.

**R1. The leaves.**
- `keyIndex.restore` (an empty key index gets one generation `{created, ver, [modified]}`;
  panics on a non-empty one) and `keyIndex.restoreTombstone`, against the key index's model in
  `InvIndex*.lean`. With no compaction a key's first revision is a put whose `CreateRevision` is
  that revision and `Version` is `1`, so `restore` agrees with `put` on an empty key index: state
  that as the lemma the rebuild uses; `restoreTombstone` is then unreachable (a key's first entry
  is never a tombstone without compaction) and needs a spec for the branch only.
- `restoreChunk`: per key, `proto.Unmarshal` (`Spec/google_golang_org/protobuf/proto/Unmarshal.lean`)
  of the bucket's value gives the change's `KeyValue` (the bucket's values are the encodings
  `bucketMap` records); `keyToLease` stays empty (no lease: `restoreLogOk`, the tombstone and
  no-lease branches delete from an empty map); the send through R1's channel protocol.
- The channel protocol: `rkvc` as a buffered SPSC channel (Perennial's `Spsc` idiom: a per-position
  predicate `P i v` "the `i`-th change of the bucket's ordered entries", the final `R` "all of them
  sent"), `revc` as a one-shot result (Perennial's `Future` idiom, or `Spsc` with one value): the
  goroutine's answer, the last revision, with the index back.

**R2. `setupMetricsReporter`.** The gap the spec check found: it writes five package globals
(`reportDbTotalSizeInBytes`, `reportDbTotalSizeInUseInBytes`, `reportDbOpenReadTxN`,
`reportCurrentRev`, `reportCompactRev`) under five package mutexes, which `restore`'s axiom owns
none of (as `publishV3` closed `readych` before 2026-10-23). The package facts must hold each mutex
with its global (`sync.isMutex` over `global ↦ f`, from the package's initialization: mvcc's
`Init.lean` through `etc/gen-init.py`'s `SPECIAL`), so that the proof stores a closure under each.
The closures themselves (they read `b.Size()` and `s.revMu`) run only from Prometheus's collector,
which no verified code calls: store any closure, with no spec on it.

**R3. `restoreIntoIndex`.** The goroutine's loop invariant over the changes received so far: the
index is the history of the log's prefix of those changes (`restoreIdxPre`/`restoreIdxPost`, the
spec's per-change receipts, D22h), and every cached key index is the index's for its key (the
cache only shortens `idx.KeyIndex`). The purge keeps that (it only deletes). `verify.Verify`'s
check holds (revisions arrive in order: `UnsafeRange` returns keys sorted). `treeIndex.KeyIndex`
and `treeIndex.Insert` are translated and specified (`InvIndex*.lean`).

**R4. `store.restore`.** The chunk loop: the cursor `min` past every key handed to
`restoreChunk`, the keys of the bucket below it sent in order (`readTx.UnsafeRange`'s spec over the
`Key` bucket's view, `bucketView`, with a limit); a short chunk ends it. The compaction reads find
nothing (`kbNoCmp`), so `compactMainRev` stays `-1` and no compaction is resumed. `currentRev` is
`revc`'s value, `|L'| - 1` (R3; the raises do not fire). The lease loop ranges over an empty map.
- **Design point (R4a): `s.revMu` in the spec.** The spec takes `s.revMu ↦ zero_val sync.RWMutex`
  and gives it back so, with `currentRev` and `compactMainRev` as plain points-to, but the body
  locks and unlocks `revMu` around its writes; a proof cannot hand a mutex back as plain memory
  once used as a lock. Either the spec takes the lock with a caller-chosen invariant over the two
  fields (`NewStore`'s `revMuInv` in its boot mode, `Restore`'s restoring mode, as `Restore`
  already has it), or `NewStore` initializes its lock before `restore` and passes it in. Decide
  before R4; `NewStore`'s proof follows the choice.
- Then `mvcc.store.restore.wp_proof` is a theorem; `NewStore` and `Restore` use it unchanged in
  shape (R4a aside).

**R5. `store.Restore`.** The translated body over R4's spec, the ghost moves its spec's "why it is
true" paragraph lists, as `InvStore` lemmas:
- gather `cur`'s seven parts under `s.mu` (the writer's eighth from `writerInv`, the readers'
  pool's eighth with no slot out, the closer's, `revMuInv`'s, the shares');
- `newTreeIndex` with a spec over the store's history and committed-log names and fresh
  event-count and compactor names (today's spec takes `idxFresh`: add the variant, as
  `newTreeIndex.spec` is used by `NewStore`);
- `revMu` into restoring mode and out (S3's `revMuRest`), around R4;
- move the committed log, its authority, the index's history and the revision budget from `L` to
  `L'` (`L <+: L'`, `histOf` prefix-monotone), refill the readers' pool at the new index and
  backend, and put the writer's state at `L'` with the registration pending (`writerReg`).
Then `mvcc.store.Restore.wp_proof` is a theorem; `watchableStore.Restore` uses it unchanged.

**R6. Close.** `etc/tcb-report.py --check --update` (537), the fingerprint (no closed theorem
changed; `restore`'s spec changes with R4a, an intermediate spec), `etc/gates.sh`,
`notes/STATUS.md`, a decision entry for R4a.

## Order and size

R0 first (the translation decides R1-R4's shapes). R1 and R2 are independent. R3 needs R1's
channel protocol; R4 needs R1-R3 and R4a's decision; R5 needs R4. R5 is the largest: its ghost
moves are what S1-S5 of D22's receiver epochs designed `isStore` for, but none is proved yet.

## Risks

- Goose on `restoreIntoIndex`'s goroutine (`defer` of a send inside a `go func`) and on
  `revKeyValue`; if it does not translate, a minimal rewrite in the etcd fork (as for other
  functions), with a regression test.
- `readTx.UnsafeRange` with a limit over the `Key` bucket: the existing spec must give the chunk as
  the first `limit` keys of the view at or above `min`, sorted; if it is weaker, strengthen it (it
  is a backend trust-boundary spec: say why it is true of bbolt's cursor).
- The per-change receipts (D22h): `restore`'s spec already pays one per change through
  `restoreIdxPre`; the goroutine must carry them across the channel (in `Spsc`'s `P`).

## Observed, not in scope

During `Restore`, `currentRev` is `1` until `restore` ends, and two unverified readers of `revMu`
do not hold `s.mu`: the metrics closures (etcd's comment: "During restore the metrics might report
'special' values") and `hashStorage.HashByRev` (the Maintenance service's `HashKV`, the corruption
checker). A `HashKV` served during a snapshot restore may report revision `1`; not reproduced, not
in `issues/`.
