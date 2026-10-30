# mvccrand: a randomized tester of mvcc in isolation, and why its adequacy is not provable

2026-10-30, branch `worktree-mvcc-rand-tester`. The user asked for a top-level randomized tester of
etcd's mvcc package in isolation, its adequacy proved end to end from the existing mvcc specs, or,
if that is impossible, why the specs are insufficient. The tester is written; the proof is not
attempted: the specs on `lean` cannot carry it. This note is the reasons, checked against the
specs at `lean` `b1712c2187`.

## The tester (`examples/mvccrand`)

`Run(cfg)` opens a backend in a fresh file (`backend.New`), a store over it with no lessor
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

## Why its adequacy cannot be proved from the specs

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
