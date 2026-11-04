# Axiom review: `backend.backend.Snapshot.wp_proof`, the compaction keys' values (2026-11-04)

**Reviewed.** `backend.backend.Snapshot.wp_proof : backend.backend.Snapshot.spec`
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean:54`, the triple in
`Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`), as strengthened by
`648d8e2bf4` (branch `mvcc-api`; the user's decision on round 16's F1 of the mvcc API review):

- the observation also receives `fkdOwn γ v`, the batch lock's half of the ghost variable `γ.fkd`
  (`ghostVar γ.fkd ½ v`, `InvBackend.lean:432`);
- `Q` takes a fourth argument, and the post applies it to `fkVals D`, bbolt's committed values at
  `meta`/`scheduledCompactRev` and `meta`/`finishedCompactRev` (`Model2.lean:475`).

Also reviewed, as the ghost representation the new clause rests on:

- `fkHalf` (the lock's half at `fkVals st.S`, the writer's contents) and `fkOwn` (the client's half
  inside the flag's client resource);
- `fkHalf_raise`/`fkHalf_put` (both halves updated on a put of a compaction key), `fkHalf_mono`
  with `fkVals_put`/`_del`/`_create`/`_delBucket` (every other operation keeps them);
- `commit_ghost` (`InvCommit.lean:32`, `commitSt_S`: a commit keeps `S`), `batchLocked_fkd` (the
  client's agreement law);
- the constructor's allocation (`backend_init`, `NewAlloc.lean:533`, at `fkVals D` of the opened
  data);
- the write specs' premises: `UnsafePut`'s `fkPut`; `¬ fkKey` in `UnsafeSeqPut`/`UnsafeDelete`;
  `∀ k, ¬ fkKey bi.name k` in `UnsafeDeleteBucket`.

The other clauses (`viewAt`, `hkOwn`, `rbOwn`, `fkRd`) are covered by [snapshot](snapshot.md) and
[backend-snapshot-fk](backend-snapshot-fk.md). They come in here only where the new clause
interacts with them.

Go code: `server/storage/backend/{backend.go,batch_tx.go}` at the etcd pin (`upamanyus/etcd`
`ce3dbc097`). The relevant parts are `batchTx.commit` (`batch_tx.go:281-308`),
`batchTxBuffered.Unlock`/`commit`/`unsafeCommit` (`:328-400`) and `backend.Snapshot`.

**Verdict: survives.** I found no gap, so there is no counterexample program and no Lean proof
was built. The docstring's argument is right. Two Go tests (below) check the clause's
non-trivial instance at the pin, and both pass.

## Why it is sound

The clause is sound if one thing holds. At the moment the axiom picks, the lock's half of `γ.fkd`
is at `fkVals D`, alongside the resources the axiom already claims there. That moment is either
the end of the last bbolt commit before `Begin(false)`, or the call's own `Commit` finding nothing
pending.

**The lock's half tracks bbolt's write transaction.** It is always `fkdOwn γ (fkVals st.S)`, and
`st.S` is the writer's bbolt contents (`btW`/`ownWTxG`).
- Every operation that changes `S` without a compaction-key put keeps `fkVals S`. These are proved
  lemmas, used in the proved method bodies, not trusted.
- A compaction-key put moves both halves together (`ghostVar_update_halves`).
- A commit and a write-back leave `S`, so they leave the half (`commitSt_S`, `wbSt`).
- So the half is never trusted to track anything. Only "S at that moment is bbolt's committed
  data" is trusted, and that is the claim the existing `hkOwn`/`rbOwn` clauses already make.

**At a real commit, `S` is what bbolt commits.** `commit_ghost` takes `C' = st'.S`, the state
after the hook's puts. Those puts went through the same methods and also keep or raise the half.

**At a no-op own commit, `S` is the committed data.** The no-op is `pending == 0`, checked after
the hook ran (`batch_tx.go:284`). The model's invariant does not say `pend = 0 → S = C`:
`commit_ghost` allows `C' = st'.C`, and `sessWf`'s agreement is only off the hook's buckets, where
`meta` is not. It is still true of every real execution:
- Each write method increments `t.pending` after it writes the bbolt transaction (`:144, :156,
  :190, :246`).
- `t.pending` is reset only right after `t.tx.Commit()` (`:300`, where an error is `Fatal`), and
  a fresh `begin(true)` follows.
- So `pending == 0` means that bbolt's write transaction has nothing uncommitted.

**A commit visible before it returns.** bbolt's `Tx.Commit` writes the meta page before it
returns, so a concurrent `Begin(false)` can see the new data while the committer still holds the
lock. At that point the ghost `S` is already the data being committed, so the lock's half is
already at its values. The `γ.fkd` clause does not depend on where the commit is linearized
inside `Commit`.

**Every step from `Begin` to `Q (fkVals D)` is pure.**
- `Begin(false)` reads bbolt's latest meta. That is the call's own commit or a later one (the
  `run` goroutine's, a committing `Unlock`'s, a `ForceCommit`), so `D` is the last commit's data.
- At the end of that commit, the committer holds `W ∗ Pk` and the lock's halves at `S = D`, and
  the caller holds `R`.
- So the observation gives `Q _ _ _ (fkVals D)`.

## Attacks tried

1. **The client's half against a stale committed value.** Ruled out. This is the clause's
   non-trivial use: `R` holds `fkOwn γ n`, so the observation can prove
   `Q _ _ _ v := v = v_client`, and the post then says `fkVals D = v_client`.
   - Suppose the client put a compaction key and `Unlock`ed without a commit (`pending <
     batchLimit`, no delete pending, `batch_tx.go:355`). Then the client's half is the new value
     while bbolt's committed data still has the old one.
   - `Snapshot`'s own `b.batchTx.Commit()` commits it before `Begin`.
   - While `R` holds `fkOwn`, no other thread can put a compaction key (`fkPut` needs it). So
     every commit during the call has `fkVals S = v_client`.
   - Go agrees (`TestFkdBufferedPut`, below).
2. **The own `Commit` with nothing pending.** Covered above. With no hooks and `pending == 0`,
   nothing is committed and `D` is an earlier commit. The moment used is the own commit's check,
   where real `S = C`.
   - The test's second half (`ForceCommit`, then `Snapshot`) checks it.
   - The model's `C' = st'.C` case cannot be reached in a real execution with `S ≠ C` at the
     compaction keys.
3. **Concurrent compaction-key puts during `Snapshot`.** Ruled out.
   - A put between the last commit and `Begin` moves the lock's half away from `fkVals D`. The
     axiom does not evaluate the observation at `Begin`; it uses the end of the commit, where the
     half is at `fkVals D`.
   - A committing `Unlock` after the put is a later commit: its end is then the moment, with the
     new value both in the half and in `D`.
   - Without the client's half in `R`, `fkdOwn γ v` alone constrains nothing (one half, any `v`).
   - `TestFkdConcurrent` checks Go's bounds: 300 snapshots against a writer, with a 1 ms commit
     interval and batch limit 3.
4. **Duplicating the client's half, or a third half.** Ruled out.
   - `γ.fkd` is allocated once per backend, by `backend_init`, with exactly two halves: the lock's
     (`fkHalf`) and the client's (inside `fkOwn`, handed out once in `fkCl`).
   - No law produces an `fkOwn` or `fkdOwn` from anything else. The only consumers and producers
     are `fkHalf_raise` (one in, one out), `fkRd_abs` and `fkRd_open` (given back), and
     `ClientLaws`' `fkCl` split.
   - `fkPut` needs the whole `fkOwn`, so the client cannot spend the mono-nat half and the values'
     half separately.
5. **Agreeing wrongly.** Ruled out.
   - `batchLocked_fkd` says the client's half equals `fkVals st.S`, the writer's contents. That is
     true and says nothing of the committed data or the readers.
   - No law equates the client's half with a reader's or the committed state. The only bridge to
     committed data is this axiom, at a commit.
6. **The lock's half outside the lock, so that `R` holds it.** Not exploitable.
   - Say a caller holds `batchLocked` and `fkOwn` in `R`. The axiom's `fkdOwn` is then a third
     half, so the observation proves `False` and with it any `Q`.
   - But in Go, `Snapshot`'s `b.batchTx.Commit()` takes `t.lock()` on a mutex that is locked.
     Only `Unlock`'s spec releases it, and that needs the `batchLocked` that `R` freezes for the
     call, so the call never returns.
   - That is a deadlock, not a panic, and partial correctness makes the post vacuous. The same
     holds of `hkOwn`/`rbOwn` ([snapshot](snapshot.md), "vacuous observations").
   - `Close` consumes `bOpen γ 1` and returns nothing of the lock's ghost, so a stopped backend
     cannot be snapshotted.
7. **Compaction-key writes outside `UnsafePut`.** Each is excluded.
   - `UnsafeSeqPut` and `UnsafeDelete` have the premise `¬ fkKey bi.name kb`.
   - `UnsafeDeleteBucket` has `∀ k, ¬ fkKey bi.name k`, which excludes `meta`.
   - `UnsafeCreateBucket` is bbolt's `CreateBucketIfNotExists`: it keeps an existing `meta` and
     creates an empty one otherwise. Both keep `fkVals`, as the model's `create` says.
   - The raw `batchTx` methods (`batchTx.UnsafePut` on `btW`) are not reachable from outside the
     package. `batchTxBuffered` overrides every `UnsafeWriter` method, and `BatchTx()` returns the
     buffered one.
   - The pre-commit hook writes through the same buffered methods. etcd's hook writes
     `consistent_index`, `term` and `confState`, not compaction keys; an `fkKey` put from the
     hook would need `fkOwn` in `Pk`, and would then move both halves.
   - `UnsafePut` keeps its value slice by reference until the commit, and the spec takes
     `value ↦*□ vb`, so the client cannot rewrite it under bbolt.
8. **Arbitrary data at the open** (`OpenSnapshotBackend`, `OpenBackend`). Ruled out.
   - The constructor allocates `γ.fkd` at `fkVals D`, where `D` is `fileHolds`'s data. It is
     proved (`backend_init`, through `New`), with fresh names per backend.
   - Any values, or none, are fine: the ghost only records them.
   - Whether the model's `D` is faithful to an arbitrary file (for example a nested bucket at a
     compaction key) is the bbolt open axioms' question ([openbackend-recs](openbackend-recs.md)).
9. **The buffers.** Not an issue. bbolt's read transaction does not see the read or write buffer,
   and `fkVals` is of `S`/`D`, both bbolt data, never of a buffer.

## The Go tests

Written as `server/storage/backend/fkd_review_test.go` in a scratch checkout of the etcd pin
(`/tmp/fkd-review/etcd`, not in this repository). Run with `GOTOOLCHAIN=go1.27.3 go test
./storage/backend/ -run TestFkd -count=5`:

- `TestFkdBufferedPut`: a batch limit of 10000 and an interval of one hour. It runs
  `UnsafeCreateBucket(Meta)`, then `UnsafePut(Meta, "scheduledCompactRev", "v1")` and `Unlock`,
  with no commit. A `Snapshot` written out and reopened then reads `v1`. A second put, followed by
  `ForceCommit` and `Snapshot` (whose own commit is a no-op), reads `v2`.
- `TestFkdConcurrent`: a writer goroutine puts `finishedCompactRev = i` for `i = 1, 2, …` under
  the lock. There are 300 snapshots; each reads a value between the last put before the call and
  the last put after it, plus one.

Result: `ok go.etcd.io/etcd/server/v3/storage/backend 3.790s` (5 runs, both pass).

## Not tried

- **Defragmentation.** It is unspecified, so no proof can call it. Note that this etcd's
  `Defrag` is documented as non-blocking with respect to `LockForSafeRangeDelete`
  (`backend.go:77-83`). Specifying it would need this clause re-argued: it copies the committed
  data, replaces `b.db` and begins a new write transaction.
- **The bbolt predicates.** The slices returned by `UnsafeRange` are handed out at a fraction
  `∃ dq` chosen by the proved code (`batchTxBuffered.UnsafeRange`'s post). Whether that fraction
  could be whole over an mmap'd page is the bbolt model's question ([bbolt](bbolt.md)), not this
  clause's.
- **A Lean proof of a client.** I built nothing: there was no `lake` run (one was in progress).
