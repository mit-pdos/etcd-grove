# mvccrand: a randomized tester of mvcc, used as etcd's server uses it

Branch `worktree-mvcc-rand-tester`. 2026-10-30: the user asked for a top-level randomized tester of
etcd's mvcc package in isolation, its adequacy proved end to end from the existing mvcc specs, or,
if that is impossible, why the specs are insufficient. The first version (below, "The first
version") exercised mvcc beyond what etcd's proof relies on; its adequacy is not provable from the
specs on `lean` (`b1712c2187`), for the reasons listed there. 2026-11-01: rewritten, at the user's
request, to exercise what etcd relies on; no proof attempted yet.

## What etcd relies on mvcc for

From etcd's calls (non-test, at the pin) and the mvcc results its proofs link (the server's, the
apply, txn and v3rpc `Link.lean`s):

- **One writer, the apply thread**, through the txn package: `Put` and `DeleteRange` (a write
  transaction, reading the previous key-values first: `checkAndGetPrevKV`); `Txn` (the compares
  in a read transaction, shared-buffer mode when it writes and the feature is on, `End`, then a
  write transaction, which must start at the read's revision: txn.go, "writes are serialized on
  the raft loop", or `NewReadOnlyTxnWrite` of the read when it does not write; ranges in the write
  transaction see its pending changes); lease `Grant`/`Revoke` (the revoke deletes the lease's keys
  through mvcc's range deleter, `s.Write`, in one revision); `KV().Commit()`. (Correction,
  2026-11-01: etcd's proof excludes every lease request from its workload, `rqOk`'s
  `leaseGrant`/`leaseRevoke`/`leaseCheckpoint` are `False`, D14h; its `Revoke` contract is vacuous.
  So the leases are in etcd's Go use but not in what its proof relies on.)
- **The post-lock hook** (`getTxPostLockInsideApplyHook`, the consistent index's save), installed
  on the backend after `mvcc.New`, run in every write's lock (`LockInsideApply`).
- **Request goroutines reading concurrently with the writer**: `Read(ConcurrentReadTxMode)` with
  the floor of a linearizable read (`store.Read`'s `log₀`), read-only `Txn`, `Rev` for headers.
- **Watches** (v3rpc): a stream per connection, whose receive loop registers watchers (`Watch`,
  `RequestProgress`, `RequestProgressAll`) and whose send loop drains `Chan()`.
- The watchable store (`mvcc.New`) over the real backend and the real lessor.
- **Not relied on** by the current proof: compaction (the store is never compacted), the store's
  own `Put`/`DeleteRange`/`Range` (`Range`'s one caller, the watch server's previous key-value, is
  behind `watchReqOk`), `Restore`, hashing.

## The tester (`examples/mvccrand`, second version)

`Run(cfg)` sets the store up as the server does (`backend.New` of a fresh file, `lease.NewLessor`
over it, `mvcc.New`, then `be.SetTxPostLockInsideApplyHook` of a hook saving the index being
applied, as `getTxPostLockInsideApplyHook`), then runs concurrently:

- **the writer** (`cfg.Ops` operations, the only writer): `Put` and `DeleteRange` as txn's (a
  range of the previous key-values in the write transaction first), `Txn` as txn's (a compare in a
  read transaction, shared-buffer or concurrent, then a write transaction checked to start at the
  read's revision, with 1-3 puts, deletes and ranges of the pending state; or a read-only
  `NewReadOnlyTxnWrite`), lease grants, revokes (the lease's keys deleted in one revision) and puts
  with a lease, `Commit`, the lessor's record of each key's lease and each lease's keys
  (`GetLease`, `Lookup(...).Keys()`), and reads of its own at exactly its revision. After each write
  it checks that the hook ran with its index, and the store's revision; it appends each revision to
  the shared history before the transaction's `End` and publishes it after;
- **readers** (`cfg.Readers` of `cfg.Reads`): read transactions, read-only transactions and `Rev`,
  each at least at the revision published before it started (or with no floor, a serializable
  read) and at a revision written, ranges checked exactly against the history (a single key, a
  range, from-key; current, past, future; limits, count-only, keys-only, total count);
- **a watch stream's two goroutines**: one registers `cfg.Watchers` watchers as the writer goes
  (start revision from 1 to one past the published one, so most catch up through the unsynced
  path; a range whose end is not above its key must fail with `ErrEmptyWatcherRange`) and asks for
  progress; the other drains `Chan()`. Each event must be its watcher's next change in the history
  (from its start revision, in order, all fields), at or below its response's revision; a
  watcher's progress response at `P` must follow every change up to `P` (a stream-wide one only
  checks `P`: it speaks for the watchers registered when it was made).

`Main` is `Run` at seed 1: 1000 writer operations, 4 readers of 200 reads, 8 watchers; it checks
only what arrived. `TestRun` (30 seeds of 2000 operations, 4 x 400 reads, 8 watchers) also waits
(`Drain`) for every watcher to have every event, a liveness check outside `Main`. Results at the
pin, `go test -race`: pass, about 70000 watch events checked and about 3100 reads above their
floor (a write ended while they started), 16s.

**It has teeth**: each of four bugs injected in a copy of the pinned etcd server module (2026-11-01)
fails the first seed: a read transaction one revision stale every 7 revisions (`store.Read`: "the
store's revision is not the writer's", through `Rev`), the last event of a multi-event revision
not sent to watchers ("a watcher received an event it should not have, or missed one"), the hook
not run by `LockInsideApply` ("the post-lock hook did not run in the write's lock"), and `put` not
detaching a key from its old lease (the revoke then deletes a key no longer on it).

**For a proof** (checked against the specs on `lean`, 2026-11-01; no proof attempted). This version
leaves out what blocked the first (compaction and `NoDelPutAt`, the store's own
`Put`/`DeleteRange`/`Range`, `FakeLessor`, no hook). Its core has the specs it needs:

- the setup is the server's: `mvcc.New` over the real backend, the hook installed after it
  (`SetTxPostLockInsideApplyHook` gives `plHook`, frozen by `plHook_persist`, then
  `hookIs_of_init`); the hook check from `csContract` (the writer's own triple of its closure);
- the writer: the sole writer's pin (revision tokens, `watchWriter`) for `Put`, `DeleteRange` and
  `Txn`'s read then write at the same revision; reads in the write transaction exact on the
  pending state; `store.Commit`;
- the readers: the floor through an invariant holding the published revision's certificate
  (`End` returns it); "the revision read is in the history" through the certificate map `γ.cok`:
  the writer registers each log in it (`certOkNext`, which `End` requires) in the same critical
  section as its history append, and `store.Read` returns `certOk` of the log read (the server's
  `kvCertInv` pattern);
- the watches: `watchRecvOk` (each watcher's events exactly its range's changes from its first
  revision, in order; each response's revision at or above its events'), `covFact` (an event-less
  response covers its watcher: every event up to its revision received) and `respCompl` (a `-1`
  response covers every watcher registered when it was sent: stronger than the test checks).

Not provable as written:

1. **`Watch` of a valid range succeeding**: `watchStream.Watch.spec` allows `ErrEmptyWatcherRange`
   for any range (the code returns it for an empty range or a closed stream); the test's "a watch
   failed" check needs the spec to exclude it for a non-empty range on an open stream (or the test
   to tolerate it).
2. **The leases**, which etcd's proof does not rely on (above): `NewLessor` needs a non-nil cluster
   (`clusterOk`; the test passes `nil`: a stub with `Version() == nil` would do); `Revoke`'s premise
   `□ ∀ pend (all deletes), certOkNext γ log pend` cannot be met by a caller that registers its logs
   in `γ.cok` (one log per revision), only with `certFree`, which gives up the readers' argument
   above: a spec stronger than needed, unused (the server's `Revoke` contract is vacuous); the
   `Lookup` that `NewLessor` gives returns `nil` or the lease for any id, so the checks "a live
   lease is found" and "a revoked lease is gone" are not provable (`GetLease`, `Revoke`'s keys and
   `Lease.Keys` are exact).
3. Outside mvcc, as before: `backend.New`'s possible panic, the Iris environment premises
   (`fileHolds`, `keySized`; and `NewLessor`'s pure `ckptEffectsOk`), the refuted bbolt axioms.

Not checked: the Goose translation of the test (closures, `atomic.Int64`, map iteration,
`sort.Slice`/`sort.Strings`, which leave with the leases).

## The first version (2026-10-30)

`Run(cfg)` opened a backend in a fresh file (`backend.New`), a store over it with no lessor
(`mvcc.NewStore(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})`, as mvcc's own tests), and runs
`cfg.Ops` operations from a splitmix64 generator seeded with `cfg.Seed`, each checked against a
model that keeps the state at every revision (`states[r]`); a failed check panics. `Main` is
`Run` at seed 1, 2000 operations, in `mvccrand.db` (the adequacy theorem's program).

- Write transactions (`Write` ... `End`) of 1-3 puts and range deletes, with range reads inside
  them (the pending state, at the pending revision once there is a change); the store's own `Put`
  and `DeleteRange`. Checked: `Rev()`, each put's revision, each delete's count and revision,
  `Changes()` empty or not, the store's revision after.
- Range reads in read transactions (both modes) and through the store's own `Range`: a single key,
  `[k, e)`, or from-key (`end = []byte{}`), at revision 0, negative, past, future or below the
  compaction revision, with a limit, `CountOnly`, `FastKeysOnly`, `WithTotalCount`. Checked: the
  error (`ErrFutureRev`, `ErrCompacted`), `Rev`, `Count` (the limit's cut without the total
  count), and every field of every key-value (key, value, create/mod revisions, version, lease).
- Compactions (`Compact`, then the job's channel): above the compaction revision (the current
  revision half the time), at or below it (`ErrCompacted`), past the current one (`ErrFutureRev`).

`go test ./mvccrand/` (from `examples/`): 100 seeds of 3000 operations pass at the etcd pin
(`249d76bea`), about 12s. **It has teeth**: against an older etcd checkout without upstream's
compaction fix (`keyIndex.doCompact`, etcd-io/etcd#22377, in the pin since e7bb9f2de), the first
seed dies (`rangeKeys`' `lg.Fatal("range failed to find revision pair")`,
`issues/etcd-compaction-delete-then-put.md`): its transactions delete a key and put it again in
one revision about once per 100 operations, and it compacts at such a revision several times a run.

## Why the first version's adequacy cannot be proved from the specs

### In mvcc's own specs

1. **Compaction is specified only over mvcc's assumed backend.** `store.Compact.spec` takes
   `storeCmp γ` (`kbCmp γ.kb`), false of the real backend (`kb = some d`: its model forbids deleting
   from the safe-range `Key` bucket, `StoreBackend.lean`'s header); a store over it is used frozen
   (`compactRight_freeze`). No Go code implements the assumed backend (`isKeyBackendG` at `kb =
   none`: snapshot readers, the batch lock's deposit witness, the hook, the compaction calls), so no
   program can meet `storeCmp`. Every `Compact` of the tester, and every read after one that
   expects `ErrCompacted`, is unprovable. (`notes/backend-cmp-plan.md`, M2's prerequisite, plans
   the real backend's compaction.)
2. **`store.Compact` still takes the delete-then-put premise `NoDelPutAt log rev`**, which the
   pin's fix made unnecessary (`notes/m2-plan.md`: dropping it is planned with M2's re-proof of
   `doCompact`). The tester compacts at such revisions (they are correct now), so with (1) solved
   those steps would still be unprovable. The spec is weaker than the code.
3. **A store whose backend has no post-lock hook cannot write.** Every write spec (`store.Write`,
   `writeView.Put`/`DeleteRange`) takes `hookIs γ P f`, which over the real backend is
   `bkHookIs`: the backend's hook frozen (`plHookRO`) to a non-nil function (`g ≠ func.nil`;
   `NewStore_backend` takes `hf : f ≠ func.nil`). Only etcdserver installs one; mvcc's own tests and
   this tester never do, so `LockInsideApply`'s nil-hook path is not covered. (A tester could set
   a no-op hook, which is the test bent to the spec.)
4. **The lessor must be the real `*lessor`.** `isLessor le γl` is `∃ lp, le = lease.lessorIface lp
   ∗ lease.lessorPin γl lp ∗ …`: `&lease.FakeLessor{}` and `nil` are excluded (`NewStore` itself
   checks `s.le != nil`), and the only lessor constructor spec (`lease.NewLessor`) is over the real
   backend, with its tracked-bucket rights (`rbOwn`). mvcc cannot be tested apart from the lessor.
5. **The store's own `Put`, `DeleteRange` and `Range` (`writeView`, `readView`) do not pin the log
   they run at.** Their posts are `∃ ilog, idxCert γ.idx (ilog ++ …)` and `∃ log, idxCert γ.idx
   log`, with no revision tokens or certificate in the pre, unlike `store.Read`/`store.Rev`/
   `store.Write` (whose pin at the sole writer is txn's `SoleWriter.lean`: `soleWriter_pins_read`,
   `pinned_sole`). A certificate only orders logs by prefix, so the spec allows a stale or a future
   log: the tester's checks of these three calls (revision, count, key-values) are unprovable. The
   transaction-level checks are not blocked by this: `rangeOutcomeC`/`rangeKvs` are exact at the
   log the transaction read, and the sole writer knows that log.
   This does not touch etcd's proofs: no proof outside mvcc uses these three specs. In etcd's Go
   code (non-test, at the pin), `s.Put`/`s.DeleteRange` have no caller; the server's txn package
   calls `kv.Write`/`kv.Read` (its `ReadView` arguments are the open transactions), and a
   linearizable read there is pinned by `store.Read`'s two bounds: `log₀ <+: log` from the
   read-index round's applied log (`KVRead.lean`, `readServed_logR`) and `idxCert γ.idx log`, a
   prefix of the log committed at the read. `s.Range` has one caller, the watch server's
   previous key-value (`v3rpc/watch.go`, `sendWatch`, `sws.watchable.Range` at `ModRevision - 1`),
   which the proof leaves unreached by its restriction `watchReqOk` (no `prev_kv` request,
   `InvWatchStream.lean`). The view `s.Rev` (`readView.Rev`, also unpinned) is called by the
   server, which uses instead the promoted `store.Rev`'s pinned spec, proved directly over
   `store.Read` (`store__Rev.lean`): the way to pin the other three.

### Outside mvcc (the backend the store needs)

6. **`backend.New`'s spec allows a panic unconditionally** (`… ∨ ⌜∃ p, r = PanicV p⌝`): bbolt's
   `Open_kv` may return an error with no premise excluding it, and `newBackend` then panics. So
   "Main does not panic" is unprovable for any tester that opens a backend. The server examples
   avoid it through the trust-boundary axiom `storage.OpenBackend.wp_proof` under the opaque
   premise `dbOpensOk` (its docstring: the panic cannot be excluded from `New`'s spec).
7. **Environment premises in Iris**: the file (`fileHolds path ∅`, an axiomatized predicate) and
   `keySized` (fewer than `2^62` `Key` entries in any read state, "a genuine assumption") would be
   Iris premises of the closed theorem, as `putget.premises` is, not the pure premises
   `notes/autoverify-plan.md` asks for.
8. Through the real backend every result rests on bbolt's axioms, two of which are refuted
   (STATUS.md, "Two bbolt axioms refuted"; neither reached by this tester's writes).

### What a provable tester would be

Through `Write`/`Read`/`Rev` only (5), no compaction (1, 2), a real lessor made by `NewLessor` over
the same backend (4), a no-op post-lock hook (3), the backend opened through `storage.OpenBackend`'s
axiom or under a new environment premise on `backend.New` (6), with Iris premises (7). That is a
weaker test than the one asked for, shaped by the specs; not written.

### What would make this tester's adequacy provable

The real backend's compaction (`notes/backend-cmp-plan.md`) and `NoDelPutAt` dropped (M2); a write
contract for a nil hook (`hookIs` over the real backend with `g = func.nil`: `LockInsideApply`
then runs nothing); `isLessor` generalized to any lessor meeting its four triples (`FakeLessor`
meets them with `I = ∅`); `writeView.Put`/`DeleteRange`, `readView.Range` taking the revision
tokens and certificate as `store.Read` does; and on the backend side, `backend.New` (bbolt's
`Open`) not failing under an environment premise.
