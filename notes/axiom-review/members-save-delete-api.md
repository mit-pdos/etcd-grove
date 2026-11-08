# The membership backend's save and delete, restated over mvcc's API (R8)

Reviewed 2026-11-07 by the `axiom` skill, on `mvcc-api` at `a271c751e3` (the specs as R8 restated
them; the old statements: `origin/lean` at `a4c2de7364`).

**Axioms.** In `Proof/go_etcd_io/etcd/server/v3/storage/schema/`, their triples in
`Spec/go_etcd_io/etcd/server/v3/storage/schema/`:
- `schema.membershipBackend.MustSaveMemberToBackend.wp_proof`
  (`membershipBackend__MustSaveMemberToBackend.lean`);
- `schema.membershipBackend.MustDeleteMemberFromBackend.wp_proof`
  (`membershipBackend__MustDeleteMemberFromBackend.lean`).

The restatement (`notes/mvcc-merge/r8.md` §4) changed only the batch lock's hook and the tokens:
- `mvcc.hookOk γ P f ∗ mvcc.csContract P f Pre Q Post` (with `γ.kb = some d`), and
  `isBackend d.γB d.P W Pk d.be` at a separate `Pk`, became
  `plHookRO d.γB f ∗ ⌜f ≠ func.nil⌝ ∗ srvApi.csContractA P f Pre Q Post ∗
  isBackend d.γB d.P W P d.be`;
- `mvcc.storeWT γ`/`storeRT γ` became `apply.bkWT d`/`apply.bkRT d`.

The buckets (`rbPart`/`rbOwnIn`, `bkPut`/`bkDel`), the member's encoding and the bucket-existence
premises did not change; earlier reviews covered them (`members-of-bk.md`, `members-decode.md`).

**Go code** (pin `673da07c8fab`, `server/storage/schema/membership.go:52-62, 74-82`):
`MustSaveMemberToBackend` runs `json.Marshal(m)` (and `lg.Panic` if it fails), then
`tx := be.BatchTx(); tx.LockInsideApply(); defer tx.Unlock(); tx.UnsafePut(Members, key, value)`.
`MustDeleteMemberFromBackend` does the same with `UnsafeDelete(Members, key)` followed by
`UnsafePut(MembersRemoved, key, "removed")`.

## Verdict

**The restatement survives** on the three points it was attacked on. The new hook and token
clauses are, clause by clause, the preconditions of the proved backend specs the Go body calls.
The old statement, with `Pk` free, did not line up with them that directly.

**The axioms still inherit the `ETCD_VERIFY` refutation.** This is not caused by the restatement:
the old statements had it too. Both axioms require a non-`nil` hook (`f ≠ func.nil`). With a
non-`nil` hook, `LockInsideApply` calls `ValidateCalledInsideApply`. With `ETCD_VERIFY=lock`,
that call panics whenever `.applyEntries` is not on the stack. No premise excludes either
condition. Shown in Go below; no Lean proof was built. The gap is the one `etcd-verify.md`
refuted at the leaf (`backend.ValidateCalledInsideApply`, all four of that family). Its planned
repair, a startup premise `envVerifyOff`, has to reach these two axioms as well.

## Attacks tried

### 1. `isBackend` at `P` instead of a separate `Pk`

Can a caller choose `P`/`f` so that the contract is vacuous, or so that the hook runs out of order?

- **`P` is the lock's hook resource.** `isBackend` is persistent, and its
  `sync.isMutex (muOf t) (batchFree γ P W Pk b t)` is an `isLock` (Perennial
  `Proof/sync/Base.lean:58`). Allocating an `isLock` consumes the lock location's full
  points-to, so a backend has one lock invariant. The `W` and `Pk` in it are the ones its creator
  passed to `backend.New`, which must establish `W γ ∗ Pk γ` at allocation (`New.spec`'s
  `∀ γ, hkOwn … ∗ bFresh γ ={⊤}=∗ W γ ∗ Pk γ ∗ K γ`). A caller therefore cannot invent a
  backend at `P := False`. Nor can it reach `P := True` without establishing `hooksSpec` at
  `True`, which is part of the same persistent fact.
- **The new clauses are `LockInsideApply`'s proved precondition.** The relevant spec is
  `backend.batchTxBuffered.LockInsideApply.spec` (proved, not an axiom), whose precondition is
  `isBackend γ P W Pk b ∗ bOpen γ qo ∗ plHookAt γ dq f ∗ Pre ∗
  (⌜f ≠ nil⌝ ∗ □ {{Pk ∗ Pre}} f() {{Q}})`.
  The axiom supplies each part:
  - `Pk := P`, from `isBackend … W P d.be`;
  - `plHookAt γ DFrac.discard f`, which is `plHookRO`;
  - `bOpen γ rdOpen`, which is `bkRT`'s second half;
  - the `□` triple, which is `hookRun P f Pre Q` at `f ≠ nil`.

  So the hook part of the contract is no stronger than the proved spec of the function Go calls.
  This holds for any `P`, `W` and `f` the caller can produce.
- **The old statement was looser.** The old precondition had the hook triple over the store's
  `P` (`hookP γ P`, a saved proposition), and `isBackend` at an unrelated `Pk`. Only the store's
  invariant, which is not in the precondition, tied the two together. The new statement removes
  that gap. Against the old statement, the new one is weaker on this point, not stronger.
- **Hook order.** The hook runs exactly once, right after `t.lock()` (`batch_tx.go:111-121`), and
  before `UnsafePut`. The contract matches that order. `Post` comes only through
  `Q ={⊤}=∗ P ∗ Post`, and `Q` only from the hook's triple. `P` must be returned before `Unlock`,
  where the commit hooks (`hooksSpec … Pk`, run by `unsafeCommit` when a delete is pending or the
  batch limit is reached) take it again. A caller cannot get `Post` without the hook having run.
- **`f` is the backend's hook.** `plHookRO d.γB f` is the discarded share of the backend's own
  hook variable, which agrees with the Go field `txPostLockInsideApplyHook` (backend invariant).
  `f ≠ nil` selects the branch where Go does call it.
- **The ghost names.** `d` is now chosen freely, where before it was `γ.kb = some d`. But
  `isBackend d.γB d.P W P d.be` and `mbF be ↦□ … d.be` pin `d.γB`, `d.P` and `d.be` to the one
  real backend behind `mb`, as the round-3 note in the docstring intends.

### 2. `bkWT d` / `bkRT d` in place of `storeWT γ` / `storeRT γ`

- **The definitions are the same.** On `lean`, `storeWT γ = kbWT γ.kb` and
  `kbWT (some d) = backend.wbTok d.γB`, which is `apply.bkWT d`. Likewise
  `storeRT γ = kbRT (some d) = rdTok d.γB d.P d.be ∗ bOpen d.γB rdOpen`, which is `apply.bkRT d`
  (`apply/Contracts.lean:127-132`).
- **The write token is spent.** `batchTxBuffered.Unlock.spec` (proved) takes `wbTok γ` and does
  not return it. This is the write-back's version bump (`Unlock` writes back when
  `pending != 0`, `batch_tx.go:328-334`). The axiom spends it too, on both paths. Delete
  always has pending writes. Save always has a put.
- **The reader token is lent.** Its `bOpen` share is what `LockInsideApply` needs. It excludes
  `bStopped`: `bOpen` holds `opn` at `false`, `bStopped` is `opn` at `true` discarded. The
  stopped branch is the one where `batchTx.tx` is `nil` and `UnsafePut` would dereference
  `nil`. `Close` needs the whole of `γ.cls`, so the lent share keeps the backend open for the
  call. The `rdTok` half is used by none of the specs Go calls here: `Unlock` takes `readTx`'s
  writer lock, not a reader slot. Lending it and returning it unchanged only strengthens the
  precondition.

### 3. Other writers, and mvcc's reader tokens

- **Other writers under the same batch lock.** mvcc's `KV.Write`, the lessor, auth and the
  consistent index all take the batch mutex. In Go a concurrent writer can make this call block,
  never panic. In the logic, the lock invariant is acquired through `LockInsideApply` as above,
  and the buckets are exclusive by `rbPart` (per tracked bucket, `rbEls`). The post-lock hook the
  server installs only sets the consistent index's atomics; the commit hooks write their own
  keys under `hkOwn`. These parts are the same as in the old statement.
- **No mvcc reader token is taken.** Is that sound? Yes. The Go body opens no read transaction:
  `UnsafePut` and `UnsafeDelete` act on the batch transaction. `Unlock`'s write-back takes
  `readTx.Lock()`, a writer lock that blocks and does not panic. mvcc's reader tokens
  (`mvccReaders`) account for mvcc's store's read pool, which this call does not touch. The
  backend's reader slot (`bkRT d`'s `rdTok`) is a linear resource. It is lent and returned, never
  duplicated, so whichever pool it came from (the apply thread's `bkRTOf`) loses nothing. The old
  statement took `storeRT γ`, the same resource, and no `mvccReaders` either.

### 4. The rest of the body, re-checked

- **`json.Marshal(m)`** cannot fail on `membership.Member`: strings, slices of strings, a bool and
  a `uint64`. The invalid-UTF-8 coercion is covered by `members-decode.md`.
- **`UnsafePut`/`UnsafeDelete` on a missing bucket** call `lg.Fatal` (`batch_tx.go:171-177`). That
  ends in `os.Exit`, not a panic. The premises `(bk.lookup …).isSome` exclude it in any case.
- **A commit's bbolt error** also ends in `lg.Fatal`, so it is not a counterexample.

## The `ETCD_VERIFY` path (inherited, Go only)

Scratch module `/tmp/axcx-memb` (not committed): `memb_test.go`. Each test creates a fresh
temporary backend (`betesting.NewDefaultTmpBackend`), creates the `members` and `members_removed`
buckets, and installs a non-`nil` hook (`func() {}`), as the axioms require. It then calls
`MustSaveMemberToBackend(&Member{ID: 1})` or `MustDeleteMemberFromBackend(1)` from a test
function, with `ETCD_VERIFY` unset or set to `lock`. Output (`go test -count=1 -v`, go1.27.3,
the pinned fork `673da07c8fab`; zap's stack traces trimmed):

```
=== RUN   TestSaveUnset
    memb_test.go:33: returned
--- PASS: TestSaveUnset (0.00s)
=== RUN   TestSaveLock
    logger.go:146: PANIC	Called outside of APPLY!	{"stacktrace": "…ValidateCalledInsideApply verify.go:36
        …(*batchTx).LockInsideApply batch_tx.go:119
        …(*membershipBackend).MustSaveMemberToBackend membership.go:58 …"}
    memb_test.go:31: panicked: Called outside of APPLY!
--- PASS: TestSaveLock (0.00s)
=== RUN   TestDeleteUnset
    memb_test.go:33: returned
--- PASS: TestDeleteUnset (0.00s)
=== RUN   TestDeleteLock
    logger.go:146: PANIC	Called outside of APPLY!	{"stacktrace": "…ValidateCalledInsideApply verify.go:36
        …(*batchTx).LockInsideApply batch_tx.go:119
        …(*membershipBackend).MustDeleteMemberFromBackend membership.go:77 …"}
    memb_test.go:31: panicked: Called outside of APPLY!
--- PASS: TestDeleteLock (0.00s)
ok  	axcxmemb	0.030s
```

The panic is deterministic. A side effect, seen in a first version of the test that reused one
backend: the panic leaves the batch lock held, because `defer tx.Unlock()` is not yet
registered. A later call on that backend, or its `Close`, then deadlocks.

All the other premises are met: a real backend, the buckets present, a non-`nil` frozen hook.
So a Lean counterexample would need only the backend's construction specs (`New`, the bucket
creation, `SetTxPostLockInsideApplyHook`, `plHook_persist`) and these axioms. It was not built:
the refutation is the leaf's (`etcd-verify.md`) and adds nothing to it.

**Proposed fix (not applied):** when the `ETCD_VERIFY` repair lands (`envVerifyOff`), add it as a
premise of both axioms, or derive it from the server's startup fact through `applyConfChange`.
The other choice is to prove both axioms through `LockInsideApply`/`UnsafePut`/`Unlock`, which
would inherit the repair from `ValidateCalledInsideApply`'s restated spec.

## Not tried

- Proving the axioms from the backend's specs. What stops that proof is `Unlock`'s view
  obligation (`thinV …` or `bView`), `UnsafePut`'s `fkPut`/`hkPut` and its pending bound. That is
  the D43 M5b′ decision ("a contract axiom over the tracked buckets, not proved through the batch
  lock's hook"), and the restatement does not touch it.
- The bucket-level claims (`rbOwnIn` idle, other buckets of `S` unchanged). Unchanged since
  `members-of-bk.md`, and not attacked again here.
