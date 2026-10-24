# Plan: prove `store.restore` and close `store.Restore`

Status: R0 done (2026-10-23, branch `restore-r0`); R1 done (2026-10-23, branch `restore-r1`, see
"R1's findings"); R3 done (2026-10-23, branch `restore-r3`, see "R3's progress"); R2 done and R4 done
for the empty bucket (2026-10-23, branches `restore-r4`, `restore-r4b`, see "R4's progress"); R5
(with `restore` of a bucket with data), R6 to do. Removes two of mvcc's trust-boundary axioms,
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

**R3's design point: who owns the index during the rebuild** (found 2026-10-23, starting R3).
The goroutine calls `put`/`tombstone` on cached key indexes *outside* the tree's lock
(`kiCache`), but `isTreeIndex`'s lock invariant (`idxLockInv`) owns every key index's contents.
So during the rebuild the index cannot be a lock-protected `isTreeIndex`. etcd is right to do
this: nothing else can reach the index then (`NewStore` has not returned; `Restore` holds `s.mu`).
Chosen: **the index stays private memory until the rebuild ends.** `newTreeIndex` returns the
tree and its `RWMutex` as plain memory owned by the caller; the goroutine owns them while it
runs (`KeyIndex`/`Insert` lock and unlock a mutex nobody else can reach) and hands them back on
`revc`; `store.restore` then allocates the lock (`init_RWMutex`) with `idxLockInv` at the
rebuilt log. This needs sequential specs of `RWMutex`'s `RLock`/`RUnlock`/`Lock`/`Unlock` on
memory no one else can reach (proved here over Perennial's translation of `sync`, a Perennial
gap recorded in `notes/perennial-changes.md`). The same specs settle R4a for `NewStore`, where
`s.revMu` is private memory too while `restore` runs; not for `Restore`, where `s.revMu` stays a
live lock (`hashStorage.HashByRev` reads it without `s.mu`) with its restoring mode, so
`restore`'s spec takes the lock in one of two ways. Rejected: a restoring mode inside
`idxLockInv` (handing the contents back into the lock at the end needs a lock operation the code
does not make).

**R3's progress (2026-10-23, branch `restore-r3`).** Done, no axiom added:
1. *A generation's `created` is its main revision in the model* (the decision after R1:
   `Gen.created : w64`, `ownGen` constrains the Go field's `Main` only). `keyIndex.get`,
   `treeIndex.unsafeGet`, `treeIndex.Get` and `treeIndex.Range` now return created revisions with
   an unconstrained sub-revision; their callers (`put`, `rangeKeys`, `deleteRange`) read the main
   revision only. This also makes the `store.restore` axiom's postcondition true (it claimed the
   rebuilt index equal to the replayed one, which differed in `created`'s sub-revision).
2. `PlainRWMutex.lean`: `RLock`/`RUnlock`/`Lock`/`Unlock` (and the trusted `Mutex`'s
   `Lock`/`Unlock`) on private memory, proved.
3. `IdxPriv.lean` (`ownIdxPriv`): `treeIndex.KeyIndex` and `treeIndex.Insert` restated on a
   private index (their live-index specs were used by no proof; their only caller is the
   goroutine).
4. `restoreIntoIndex` proved (`InvRestore.lean`'s `rkvProt`/`revProt`, `idxRestore`): for bucket
   entries `ents` in increasing revision order (`RestoreEntsOk`), the goroutine answers on
   `revc` with the last revision, the private index at `idxRestore ents` (the code's own fold:
   `put`/`tombstone` on a key the index has, `restore`/`restoreTombstone` on a new one), the
   reader's token back and a receipt per entry. The cache (`rstCacheOk`), its purge and the
   lookups through the tree are covered.

5. R3b, `RestoreModel.lean`: `idxRestore (logEnts log 0 log.length) = indexOf (evsOf log)`
   (`idxRestore_logEnts'`) for a well-formed log (`LogWf'`), pure: a new key's first entry is a
   put with version `1` and its own main revision as create revision, so `restore` agrees with
   `put` on a fresh key index; a tombstone is never a key's first entry (a delete only of a
   present key). The state/index correspondence in the middle of a revision is `rev_step`'s.

What R4 takes from R3: `restoreIntoIndex`'s spec with `ents := logEnts ([[], []] ++ R) 0 _`
(`RestoreEntsOk` from `logEnts`' order, `logEnts_keys_sorted`-style), `idxRestore_logEnts'` to
turn the returned index into `indexOf (evsOf log)`, and `init_RWMutex` on the private index
with `idxLockInv` at that log.

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

**R4's progress (2026-10-23, branch `restore-r4`).**
1. *Stage 1, done*: `newTreeIndex` returns the private index (`ownIdxPriv`) and the lock's ghost
   part (`idxLockG γ 0`); `store.restore`'s spec (still the axiom) takes them, with the writer's
   handle and the caller's half of the committed log's authority at `[[], []]`, and gives back
   `isTreeIndex` with every reader's token, the writer's handle, that half and the certificate at
   `[[], []] ++ R` (`idx_publish`, `IdxPriv.lean`, makes the lock). It takes the whole of
   `currentRev`: the old spec let it write `currentRev` with half of it when `R = []` ("modelled
   as no write"), which no proof can do. `NewStore` locks `s.mu` as private memory
   (`PlainRWMutex.lean`) and makes `s.mu`'s invariant (whose `physOk` names the index), the readers'
   pool and the writer's invariant after `restore`. R4a for `NewStore` is settled by the same
   specs: `restore` takes `s.revMu` as plain memory and gives it back so.
2. *R2, done*: the five reporters and their locks translated, the package's facts hold each lock
   as a guarded `RWMutex` (`reportVar`, made by mvcc's initializer), `setupMetricsReporter` proved.
3. *Left: `restore`'s own proof*, which needs three extensions of the backend's contract
   (`isKeyBackendG`, `keyReadSnap`/`keyReadLocked`, proved of the real backend in
   `BackendBridge.lean`), each a design decision:
   - **(R4b) a limited range read.** `restore` reads the `Key` bucket in chunks
     (`UnsafeRange(Key, min, max, restoreChunkKeys)`); `keyRangeReadSpec` has limit `0` only.
     Proposed: quantify it over the limit, the answer the first `limit` entries if positive
     (`takeLimit`); the bridge's cursor lemmas already have the limit (`cursorRange_window`).
     *But* the real read is a prefix only when the read buffer has no entry in the range: with
     `n` buffered entries it returns bbolt's first `limit - n`, then the buffer's
     (`issues/etcd-unsafe-range-limit-buffer.md`). So the limited contract needs a premise the
     backend's abstraction does not have yet ("nothing buffered in the `Key` bucket", true at
     `restore`: `NewStore` wrote no key, a snapshot's backend is fresh), e.g. a token of the
     store's backend that the batch lock's first `Unlock` with puts consumes.
   - **(R4c) the compaction keys under a key read transaction.** `restore` calls
     `UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` on its `ReadTx`, whose specs need
     `metaReadSpec`, which only the compaction's `metaReadTx` has. Proposed: `keyReadLocked` also
     gives `metaReadSpec` under its token; with `kbNoCmp` both find nothing (or: a variant of the
     two specs that takes `kbNoCmp` and answers "not found").
   - **(R4d) two readers of the same slices.** The goroutine reads each entry's key bytes
     (`BytesToRev`, `isTombstone` on `rkv.key`) while `restore` keeps reading the bucket, both
     under the one read transaction; `rdCap Rd Tok` lends the bytes only against the exclusive
     token `Tok` (the real one holds the transaction's read lock: `rtTok`). Proposed: a
     fractional reader's token (`rdCap` over `Tok q`), so `restore` lends a part to the goroutine
     (`restoreIntoIndex`'s spec already takes its own `Tok`, returned on `revc`); the bridge must
     show the real `rtTok` splits (the bbolt transaction's pages are immutable while it is open).
   Also needed: `RT` (a reader's token, which `ReadTx` takes) in `restore`'s spec, lent by
   `NewStore` from its slots.
4. *Option 1, done (branch `restore-r4b`)*: R4b and R4d need changes to the backend's invariant
   (an "empty read buffer" token, a split reader's token), so `restore` is proved for the bucket
   `NewStore` hands it, the empty one (`bucketView γ q ∅`), and the rest moves to R5:
   - `restore`'s spec takes the empty bucket, `RT` (lent by `NewStore` from its slots) and
     `kbNoCmp`; `mvcc.store.restore.wp_proof` is a theorem.
   - The contract has a range read with any limit, `keyRangeLimSpec`: the answer is a `Sublist`
     of the range, which is what the real read gives (a prefix of bbolt's window, then a prefix
     of the buffer's; `rtRange_sublist`, `rt_rangeLim` in `BackendBridge.lean`). Weak, but enough
     for an empty bucket (the first chunk is empty, the loop ends), and true without R4b's premise.
   - R4c: `metaReadSpec rt nc` with `nc = true` says a compaction key read finds nothing;
     `UnsafeReadFinishedCompact`/`UnsafeReadScheduledCompact` take `nc` and answer "not found"
     under it; one new axiom, `mvcc.kbNoCmp_metaNone` (`NoCmpRead.lean`): under `kbNoCmp` a key
     read transaction's `Meta` reads find no compaction key. It is an axiom because the bridge
     says nothing about the `Meta` bucket (the hook's); its docstring says why it holds.
   - `keysGauge` got `Set` (`gaugeSetSpec`, `etc/gen-init.py`).
   - Left for R5: `restore` of a bucket with data, which needs R4b's premise (or a chunk loop
     over the `Sublist` contract with a progress argument) and R4d's split token.

**R5's stages (2026-10-23, branch `restore-r5`).** `Restore` calls `restore` on a backend holding
`L'`, so R5 first does what option 1 left: `restore` with data. Six stages:
- **R5a. A clean read buffer (R4b's premise).** The backend's readers' view gets a flag
  `γ.cln : Bool`, distributed as the view `γ.view` is (the clients' half inside `bView`,
  existential there; a quarter in the batch lock's ghost share, a quarter in `readTx.mu`'s
  resource), with the invariant "flag `true` → the read buffer has nothing off the hook's buckets"
  (`rbClean`) on both sides. `bViewC γ q vd c` names the flag; `bView γ q vd` is `∃ c, bViewC …`,
  so no spec that mentions `bView` changes. Only a view-changing `Unlock` (which holds the clients'
  whole view) can falsify it; a `viewSame` one writes nothing back off the hook's buckets; a commit
  only empties the buffer. `newBackend` makes it `true` (`newPost`'s view is `bViewC … true`:
  `storage.OpenBackend`'s axiom, stated over `newPost`, promises it too, true of the code, which
  returns `newBackend`'s backend). A reader holding a share of a clean view learns the buffer is
  clean (`rtHeld_clean`), and then the limited range is the range's first `limit` entries
  (`keyRangeLimSpec`'s prefix clause, the bridge's `rtRange` with an empty buffer window).
  At mvcc: a clean view `kbViewC` (for the model instance, `kbView`), and `isKeyBackendG`'s
  `ReadTx` clause with a clean view gives the prefix clause.
  *Done (2026-10-23)*: `BNames.cln`, `RdSt.cln`, `bViewC`, `clnPart` in `rtCore`, `rbClean`
  (`Model2.lean`), `rtCore_clear_cln` (the view-changing write-back), `rbClean_writeback` (the
  `viewSame` one), `rbClean_reset` (the commit), `rtHeld_clean`; `newPost`'s view clean. At mvcc:
  `bkViewC`/`kbViewC`/`bucketViewC`, `keyRangeLimSpec`'s prefix clause (`cl`), `keyReadSnapC`,
  `keyCleanRead` and the bridge's `rtRange_clean`, `bridge_rt_clean`, `keyCleanRead_of_backend`.
  `storage.OpenBackend`'s axiom now promises the clean view through `newPost` (true: the code
  returns `newBackend`'s backend, read buffer empty). No axiom added.
- **R5b. Two readers of one read transaction (R4d).** `rtHeld` splits into a share of bbolt's
  transaction (`txLive rtx p`, enough to read its bytes: `txBytes_acc`) and the rest, and
  `readTx.UnsafeRange` works with any share; at mvcc, `keyReadLocked`'s range branch gives
  `rdSplit`: `Tok` splits into `TokA` (ranges and reads) and `TokB` (reads), both with `rdCap`.
  *Done (2026-10-23)*: `rtCore`/`rtRest`/`rtResAt`/`rtIntv` take the share `p` of bbolt's
  transaction (default `q.half`), `rtHeldF` (`rtHeld = rtHeldF … sync.rfrac.half`), `rtHeldF_lend`/
  `_return`/`_read`, `readTx.UnsafeRange` over `rtHeldF` at any share; at mvcc `rdSplit` in
  `keyReadLocked`'s range branch, proved of the real backend in `rt_locked` (`rt_rangeLimF`, a
  quarter lent). No axiom added.
- **R5c. `restore` with data.** Its spec over `R` (`bucketView γ q (bucketMap ([[], []] ++ R))`,
  clean), the chunk loop's invariant (the entries sent are the range's prefix up to `min`, `min`
  the next revision), `restoreChunk` per chunk, the goroutine with `TokB`, the leases
  (`restoreLogOk`: none), `currentRev = |L'| - 1`.
  *Done (2026-10-23)*: `store.restore`'s spec over `R` (`restoreLogOk R`; the view
  `restoreView`: for `R = []` the empty bucket, `NewStore`'s, else the clean view and
  `keyCleanRead`; the index published at `[[], []] ++ R`, `currentRev = |L'| - 1`, a receipt per
  entry), proved for both: the chunk loop's invariant (`entsFrom L' r` the entries not sent, `min`
  holding `revBytes r`), the range's prefix (`bucketRange_from`, `keyRangeLimSpec`'s `cl`), the
  next chunk after a full one (`entsFrom_next`, `BytesToRev` on the last key's first 17 bytes,
  `RevToBytes` of `revNext`), `restoreChunk` over each chunk (no lease: `logEnts_lease`), the
  goroutine's answer (`restoreLastRev_logEnts`, `idxRestore_logEnts'`, `idxCRep_indexOf`).
  `kbNoCmp_metaNone`'s premise widened to the clean snapshot (`keyReadSnapC`), the same fact. The
  code after the loop is written twice (one per exit: a tactic macro cannot hold Iris's `$$`).
- **R5d. `newTreeIndex` over the store's names** (not `idxFresh`'s): the variant `Restore` needs.
  *Done (2026-10-24)*: `newTreeIndex`'s one spec takes the event count's authority at any `n` and
  the compactor's state (fresh), with lower bounds of the compaction revision and the committed log,
  and gives the private index, `idxLockG γ n` and the compactor's token; `NewStore` splits its
  fresh names (`idxFresh_split`), `store.Restore` will make new event-count and compactor names
  around the store's (`idx_renew`).
- **R5e. The ghost moves** (the list below) as `InvStore` lemmas.
- **R5f. `Restore`'s proof** over R5c-R5e; `NewStore` and `watchableStore.Restore` unchanged.

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

## R1's findings (2026-10-23)

Proved, no axiom added: `keyIndex.restore` and `keyIndex.restoreTombstone` (specs model-agnostic:
an empty key index becomes `kiRestore created modified ver`, resp. `kiRestoreTombstone rev`, in
`Model.lean`; a non-empty one panics), and `restoreChunk` (`InvRestore.lean`'s `rkvIs` relates a
sent `revKeyValue` to its bucket entry; the spec is generic in the channel protocol `P`, a
per-entry resource `Q` that R3/R4 choose, and the read capability `Rd`/`Tok` of `rangeKeys`).
The channel protocol's instantiation moves to R3, which is where `P` is fixed.

**The lemma "`restore` agrees with `put` on an empty key index" is false as planned.**
`restoreIntoIndex` passes `created = Revision{Main: kv.CreateRevision}`, whose `Sub` is 0, while
`put` records the full revision of the key's first put. They differ when a key's first put is
not the first change of its transaction (`Sub > 0`). The model (`Lemmas.lean`, `created =
revs.head`) follows `put`. etcd's behavior is the same either way: only `created.Main` is read
(`put`'s `CreateRevision` takes `created.Main`; `keyIndex.since` compares `Revision{Main: rev}`
with `created` by `GreaterThan`, which gives the same answer for `Sub` 0 and `Sub > 0`; compaction
reads `revs`, not `created`). R3 needs a decision: (a) weaken the model's invariant to `created.main = revs.head.main` (and
`created.sub = 0` after a restore), (b) compare key indexes up to `created.sub`, or (c) state the
rebuilt index as equal to the replayed one only on what readers see.

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
