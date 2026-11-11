# Axiom review: `backend.backend.Snapshot.wp_proof`, the safe-range buckets' deleted entries (2026-11-04)

**Reviewed.** `backend.backend.Snapshot.wp_proof : backend.backend.Snapshot.spec`
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`, the triple in
`Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean:61`), as strengthened a
second time by `35fd45586d` (branch `mvcc-api`, reviewed at `c1ebffdcf1`; the user's criterion on
probe M2: a snapshot restored from gives a correct view of the abstract state it is of). The
observation now receives:

- `viewAtD γ P vd X`: the batch lock's quarter of the readers' view at a logical view `L`, with
  `vd` thin of `L` (`thinV`) and `dlVd P vd L X` (`Model2.lean`): an entry of `L` in a safe-range
  bucket (off the hook's buckets) that is missing from `vd` is in `X`, and every entry of `X` is
  such an entry, missing from `vd` and in `L`;
- `dlsOwn γ X`: the batch lock's half of the ghost variable `γ.dls` (`InvBackend.lean:523`).

Also reviewed, as the representation the new clause rests on:

- `BSess.dl` (every entry deleted from the writer's contents while present, since the open; only
  `BSess.del` changes it), its safe-range part `dlR`, and `BSess.win` (an `Unlock`'s commit window);
- `dlsOk`, `dlsS`, `dlsW` (`Model2.lean`), carried by `batchViewQ`, and `batchViewQ0` in the window;
- `fkHalf`'s `dlsOwn γ (dlR P st.dl)`, the client's half inside `fkOwn` (`∃ X, dlsOwn γ X`),
  `dlPut`, `fkHalf_dl`/`batchGhost_step_dl` (`InvBatch.lean`), `sbKept`/`dlsOk_relog`
  (`InvBackend.lean`), `dlVd_of_dlsOk` (`DlLemmas.lean:256`), `commitSt`'s `win := false`
  (`CommitLemmas.lean:226`);
- the write specs' new premises: `UnsafeDelete` (a safe-range entry of the writer's contents
  must be one the readers see; `dlPut`), `UnsafePut`/`UnsafeSeqPut` (a safe-range put not of a
  deleted entry, `st.dl.lookup (bi.name, kb) = none`), `UnsafeDeleteBucket` (`P.SB bi.name =
  false`), `Unlock`'s put branch (`sbKept`), `commit`/`unsafeCommit` (`win = true → st.win = true ∧
  dlsOk P st L'`, `st.cnt.hw = false`), `hookStep`/`hookRun` (`dlR` and `win` unchanged);
- the constructor's allocation (`backend_init`, `NewAlloc.lean:535`: `γ.dls` allocated once, at
  `dlR P ∅`, split into the lock's half and the client's in `fkCl`).

The other clauses (`viewAt`, `hkOwn`, `rbOwn`, `fkRd`, `fkdOwn`) are covered by
[snapshot](snapshot.md), [backend-snapshot-fk](backend-snapshot-fk.md) and
[backend-snapshot-fkd](backend-snapshot-fkd.md). They come in here only where the new clause
interacts with them.

Go code: `server/storage/backend/{backend.go,batch_tx.go,tx_buffer.go,read_tx.go}` at the etcd pin
(`upamanyus/etcd` `ce3dbc097`): `batchTx.Unsafe*` (`batch_tx.go:134-245`), `batchTx.commit`
(`:281-308`), `batchTxBuffered.Unlock`/`commit`/`unsafeCommit` (`:328-400`), its write methods
(`:402-426`), `backend.Snapshot` (`backend.go:381`).

**Verdict: survives.** No gap found, so no counterexample program and no Lean proof. Two Go tests
(below) check the clause's non-trivial instances at the pin; both pass.

## Why it is sound

What the axiom trusts beyond the earlier clauses is one step. At the moment it picks (the end of
the last bbolt commit before `Begin(false)`, or the own commit finding nothing pending), the batch
lock's state `st` is out of an `Unlock`'s commit window, so its quarter carries the full agreement
`dlsOk P st L`. The committed data is the writer's contents. Then `dlVd P (sData P st.S) L
(dlR P st.dl)` follows by `dlVd_of_dlsOk`, a proved lemma, and the lock's half is `dlsOwn γ (dlR P
st.dl)`.

- **Out of the window at a commit's end.** `commitSt` sets `win := false`, and `commit_ghost` takes
  `dlsS P st' ∧ dlsOk P st' L` for the `L` it leaves the quarter at. `unsafeCommit`'s premise
  requires a windowed caller to give `dlsOk P st L'` for the closing view. So the agreement at a
  commit's end is the proved code's, not trusted.
- **The physical view is the writer's contents.** `commit`'s post is proved: `vData P (st'.C,
  st'.R) = sData P st.S`, and the read buffer is reset. The hook leaves `sData` (`hookStep`). The
  no-op commit (`pending == 0`, `batch_tx.go:284`) is the case [backend-snapshot-fkd](backend-snapshot-fkd.md)
  argued: every write method increments `t.pending` (`:144, :156, :190, :246`), which only a
  bbolt commit resets (`:300`), so nothing is uncommitted. A delete increments it too, and a
  delete session's `Unlock` always commits (`pendingDeleteOperations > 0`, `:355`).
- **`dl` tracks bbolt's write transaction.** `BSess.del` records exactly what bbolt's
  `bucket.Delete` removes (the entry present in `S`). Nothing else removes a safe-range entry:
  `UnsafeDeleteBucket` excludes the safe-range buckets, `UnsafeCreateBucket` is
  `CreateBucketIfNotExists` (`:137`), and a put of a deleted entry is excluded by both put specs.
  The hook may not touch `sData` or `dlR`. So "`dl`'s safe-range entries are absent from bbolt's
  committed data" is true of Go at every commit.
- **The logical view keeps every deleted entry.** A safe-range delete needs the entry visible to
  readers (`vData`, which is thin of `L`). Then `relog` (the only way `L` loses entries) drops
  only entries the readers see, which no deleted entry is after its commit: it is absent from `C`,
  and the read buffer gets it back only through a put, which is excluded. `sbKept` excludes a put
  session that deleted a visible safe-range entry. That is `dlsOk_relog`, proved.

The remaining trust is unchanged: `D` (what `Begin(false)` sees) is the last commit's data, and
the commit's committer held the lock's shares then (bbolt's read isolation, [snapshot](snapshot.md)).

## Attacks tried

1. **`X` against what bbolt lacks: deletes buffered, not committed.** Ruled out. A safe-range
   delete changes bbolt's write transaction at once (`batch_tx.go:238`). The session's `Unlock`
   commits it before the lock is released (`:355`), with the lock held from the delete to the
   commit's end. `Snapshot`'s own `Commit` takes the lock (`:362`). So there is no commit end with
   a delete in `dl` that bbolt's committed data still has. A read transaction begun before that
   commit sees the previous commit's data, at whose end `dl` did not have the entry.
2. **The commit window.** Ruled out. In a put session's `Unlock` (writeback, then commit if
   `pending >= batchLimit`), the window state has `win = true` and only `dlsS` (`batchViewQ0`). The
   axiom never uses a window state: the commit's close (`commitSt`, `win := false`) re-establishes
   `dlsOk` at `relog P vd st` (`batchTxBuffered__Unlock.lean:232`, `dlsOk_relog`). Every step from
   bbolt's meta write to that close is under the batch lock. So the close's state is a consistent
   moment for the observation (the caller is still in `Snapshot`, holding `R`).
3. **Snapshot's own commit before `Begin`, and concurrent commits.** Ruled out, as for the earlier
   clauses. Every commit, whether from the `run` goroutine, an `Unlock` or a `ForceCommit`, is
   under the batch lock. `D` is the last one's. `TestDlsConcurrent` checks it: a deleter (one
   delete session per key, each committing at its `Unlock`) runs against an appender
   (`UnsafeSeqPut`, batch limit 3, 1 ms interval). Each of 300 snapshots' `Key` buckets is
   **exactly** `{d+1..400} ∪ {1001..p}`, with `d` within one of the deletes done around the call:
   the logical view but one commit's `X`, never more or fewer.
4. **A delete, then a put of the same key in one batch.** Excluded by the specs.
   `UnsafePut`/`UnsafeSeqPut` require `st.dl.lookup (bi.name, kb) = none` in a safe-range bucket,
   and `dl` keeps every delete since the open. In Go the put would make bbolt have the key again,
   so without the premise `dlsS` would be false. With it, it cannot happen.
5. **A put, then a delete of the same key in one batch (the read buffer's write-back of a deleted
   entry).** Handled.
   - `batchTxBuffered.UnsafeDelete` does not touch the write buffer (`:418`). So after `put k;
     delete k` the buffer still holds `k`, and `Unlock`'s writeback puts it into the read buffer
     (`:332`). bbolt lacks it.
   - If `k` was put fresh in this session, the delete is excluded: `k` is in `S` but not in
     `vData` (readers do not see the write buffer).
   - If `k` was visible through the read buffer (an earlier, uncommitted put session; a put must
     be above every committed key, so `k` is never in `C`), the delete is allowed and `dl` records
     it. `L` has it (it was visible).
   - The `Unlock` then commits (a delete pending), and `unsafeCommit` resets the read buffer
     (`:397`). The snapshot's `D` lacks `k`, and `X` has it: `dlVd` holds.
   - A snapshot never reads the read buffer, so the window in which readers see `k` again
     (writeback to commit) is invisible to it. `TestDlsImage` checks this path: after the
     `Unlock`, readers do not see `k`, and the snapshot lacks it.
6. **Duplicating the client's half.** Ruled out. `γ.dls` is allocated once per backend, by
   `backend_init`, at `∅`. It is split into the lock's half (`fkHalf`) and the client's (inside
   `fkOwn`, which `fkCl` hands out once). The only law that touches both is `fkHalf_dl`, which
   takes one `∃ f, fkOwn γ f` and gives one back. `fkPut` and `dlPut` take the same `fkOwn`, not
   a part of it. No law produces an `fkOwn` from nothing (as in [backend-snapshot-fkd](backend-snapshot-fkd.md)'s
   attack 4).
7. **Agreeing wrongly.** Ruled out.
   - Say the caller's `R` holds the client's half at `X_c`. Then the observation learns
     `X = X_c`.
   - Every safe-range delete needs `fkOwn` (`dlPut`). So while `R` holds it, no safe-range delete
     happens during the call, and every commit in it has `dlR st.dl = X_c`.
   - The same holds of `L`: an `R` holding `bView γ q vd` learns `L = vd`, and the put branch of
     `Unlock`, which needs `bView γ 1`, cannot run during the call.
   - So the post's "the `Key` bucket of `D` is `vd` but `X_c`" is the fact that held at the
     call's start, by the proved invariant.
8. **A third half, or the lock's half in `R`.** Vacuous, as before. An `R` holding
   `batchLocked` gives a third half (so `False`), but then `Snapshot`'s
   `b.batchTx.Commit()` blocks on the batch mutex the caller holds. That is a deadlock, not a
   panic. `Close` takes `bOpen γ 1`, so a stopped backend cannot be snapshotted.
9. **Deletes off the safe-range buckets, or in the hook's buckets.** Not an issue. `dlR` filters
   them out and `dlVd` constrains only safe-range entries off the hook's buckets. A visible
   non-safe-range entry deleted by a put session leaves `L` through `relog`, and `dlVd` says
   nothing of it. `hookStep`/`hookRun` keep `dlR` and `win`, and etcd's hook only puts
   (`consistent_index`, `term`, `confState`).
10. **Hidden removals: `UnsafeDeleteBucket`, `UnsafeCreateBucket`, a delete of an absent key.**
    Each is harmless.
    - `UnsafeDeleteBucket` has the premise `P.SB bi.name = false`. Without it, `L` would keep
      the bucket's entries and `dl` would not record them.
    - `UnsafeCreateBucket` keeps an existing bucket.
    - A delete of an absent key leaves `S` and `dl` (`BSess.del`'s `none` case) and is a no-op in
      bbolt (`bucket.Delete` of a missing key returns `nil`).
11. **The open.** Ruled out. `dl = ∅` and `X = ∅` at the open, with `L` the opened data's view
    (`dlsW_exact`), so `dlsOk` holds trivially. Each backend, including `OpenSnapshotBackend`'s,
    gets fresh names. The client's half is handed as `∃ X` (it does not learn `X = ∅`): weaker,
    not unsound.

## The Go tests

Written as `server/storage/backend/dls_review_test.go` in the scratch checkout of the etcd pin
(`/tmp/fkd-review/etcd`, not in this repository). Run with `GOTOOLCHAIN=go1.27.3 go test
./storage/backend/ -run TestDls -count=3`:

- `TestDlsImage`: batch limit 10000, interval one hour.
  - Keys 1..10 put in the `Key` bucket and committed. Keys 1..3 deleted in one session, whose
    `Unlock` commits.
  - The snapshot, written out and reopened, has exactly 4..10. Its own `Commit` is a no-op.
  - Then session A puts 11 with no commit. Session B puts 11 again and deletes it. After B's
    `Unlock`, readers do not see 11, and the snapshot has exactly 4..10.
- `TestDlsConcurrent`: keys 1..400 committed.
  - A deleter goroutine deletes 1..400 in order, one session each. An appender puts 1001, 1002, …
    (`UnsafeSeqPut`), with batch limit 3 and interval 1 ms.
  - Each of 300 snapshots has exactly `{d+1..400} ∪ {1001..p}`, with `d` and `p` each within the
    counts recorded before and after the call (plus one). A run's log: `d=175 in [174,177], p=2440
    in [2431,2444]`.

Result: `ok go.etcd.io/etcd/server/v3/storage/backend 8.168s` (3 runs, both pass).

## Not tried

- **Defragmentation.** It is unspecified, so no proof can call it. This fork's
  `defragNonBlocking` (`backend.go:694`) holds `safeRangeDeleteMu` for the whole call, because its
  append-only catch-up would miss a `Key` delete. A spec for it would need this clause re-argued:
  the copied data must lack exactly `X` too.
- **The bbolt model.** That `S` is bbolt's write transaction, and `bucket.Delete` removes exactly
  the entry, is the bbolt axioms' question ([bbolt](bbolt.md)).
- **A Lean proof of a client.** Nothing was built (no `lake` run: another agent was building).
- **Values.** `dlVd` is about keys only. `X`'s values (the value at deletion) are not compared with
  `L`'s, and no law claims they agree.
