# `backend.backend.Snapshot`: survives (2026-10-29)

**Reviewed:** the axiom `backend.backend.Snapshot.wp_proof`
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`, its triple in
`Spec/.../backend/backend__Snapshot.lean`), as stated on `backend-cmp` at `45977a5725`. That is after
question 2's switch: `viewAt γ vd := ∃ L, viewQ γ ¼ vd L` (`InvSnapshot.lean`), the batch lock's
quarter at a logical view that the physical view `vd` is thin of. The axiom is D22's (S-f), the
collaborator's track; this review changes nothing in it.

The Go code is etcd at the pin (the fork's `249d76bea`):
- `server/storage/backend/backend.go:381-423` (`Snapshot`), `:463-479` (`run`), `:481` (`Close`);
- `batch_tx.go:281-308` (`batchTx.commit`), `:328-372` (`Unlock`), `:374-406` (`commit`,
  `unsafeCommit`), `:418-426` (deletes).

This is the backend stage's Freeze prerequisite (`notes/backend-cmp-plan.md`, "Before Freeze, the
`axiom` skill on `backend.Snapshot`").

**Verdict: survives** every attack below. No counterexample; no Go program written.

## The claim

The caller gives an observation:
`□ ∀ vd d r, R -∗ W -∗ Pk -∗ viewAt γ vd -∗ hkOwn γ d -∗ rbOwn γ r -∗ ⌜Q vd d r⌝`.
- `R` is a resource it holds through the call and gets back.
- `W ∗ Pk` is the batch lock's client resource.
- The other three are the batch lock's ghost shares: the view's quarter, and halves of the hook's
  own keys and of the tracked buckets.

`Snapshot()` returns a snapshot open over bbolt's committed data `D` (`snapOpen sp D`) with
`Q (sData P D) (hkData P D) (rbData P D)`. In words: `Q` holds of whatever the snapshot reads,
whenever `Q` follows from those resources held together.

The axiom's own argument (its docstring):
- `D` is what the last bbolt commit before `Begin(false)` left.
- That commit is the call's own, or a later one.
- At its end the committer held `W ∗ Pk`, the lock's shares were at `C = D`, and the caller held
  `R`.
- So the resources coexisted, and `Q` follows.

## Attacks tried

1. **The four kinds of commit before `Begin(false)`** (round 11's list). The checks use the proved
   `batchTxBuffered.commit.spec`, whose post is `batchGhostAt γ P st' true` with
   `vData P (st'.C, st'.R) = sData P st.S` (the read buffer reset).
   - **`Commit`/`run`/`ForceCommit`** (`batchTxBuffered.Commit`: lock, `commit(false)`,
     `Unlock`): the lock is then free with `W ∗ Pk ∗ batchGhostAt` of the committed state. Its
     quarter is `viewAt γ (sData P C)`, and its `trkHalf` gives `hkOwn γ (hkData P C)` and
     `rbOwn γ (rbData P C)`, because the hook writes before the bbolt commit (`unsafeCommit:384`)
     and the commit makes `S` committed.
   - **`CommitAndStop`:** it ends in `bStopped`, which the caller's `bOpen γ qo` excludes. A
     backend can't stop while the snapshot's caller holds its share. In Go a `Begin` on the closed
     database fails and `lg.Fatal` exits the process: an exit, not a panic.
   - **A deleting `Unlock`** (`pendingDeleteOperations > 0`, `batch_tx.go:355`): out of a window,
     the new physical view must be thin of the logical one (the commit spec's premise).
     `viewAt γ (sData P C)` holds with the unchanged `L`, and the session hands `W ∗ Pk` back in
     `Unlock`'s precondition.
   - **A put `Unlock`'s window commit:** the bbolt commit happens before the window's close, and
     `Begin` may land between them. `W` comes from the `Unlock` caller's wand
     `bView γ 1 (relog P vd st) -∗ W ∗ Q'` at the close, where the quarter moves to `L'` with
     `sData P C` thin of it. Until the close the clients hold no share (the window holds the whole
     of it), so no observation can tie the snapshot to a view between the commit and the close.
     `Q` is a pure proposition, and it holds once the resources coexist at the close.
   - **A commit stuck before its close** never reaches the coexisting state. In Go the only steps
     between the bbolt commit and the close are `pendingDeleteOperations = 0` and
     `begin(false)`. `begin(false)` either returns or calls `lg.Fatal`, which exits. A deadlock
     there would be no counterexample either.
2. **The call's own `Commit` finding nothing pending** (`batchTx.commit:284`, an early return):
   - Deletes count in `pending` (`batch_tx.go:246`), so nothing pending means the writer's contents
     are the committed data, and the read buffer is empty (`sessWf`: `pend = 0 → R` empty).
   - With hooks, the pre-commit hook's put makes `pending > 0` anyway.
3. **A compaction's deletes pending or committed:**
   - *Pending:* deletes are not buffered (`batch_tx.go:418-421`). An uncommitted delete is in
     the write transaction only, so `D` still has the key, as the logical view does.
   - *Committed:* `D` lacks the key, which is thin of the logical view only if the key is
     registered deletable (`dlIs`). That is the commit spec's premise, proved by every committer.
     Since question 2, this is exactly what `viewAt` asks. The old exact `viewAt` would have been
     false here.
4. **The hook data and `rbOwn` in the post:**
   - Both halves track the writer's contents `S`, and at a commit's end `S` is the committed data.
   - A caller holding the client's half (`rbOwn` in `R`) gets agreement, and indeed no other
     session can change a tracked bucket without that half.
   - The pre-commit hook writes only the hook's own keys (`Meta`).
5. **A caller whose `R` contradicts `W ∗ Pk` or the shares,** making the wand vacuous (`⊢ False`)
   and so `Q := False`:
   - The call's own `Commit` locks the batch lock and so holds `W ∗ Pk` while the caller holds `R`;
     both are owned at once in every execution, so their combination is valid.
   - If the caller already holds the batch lock, `Commit`'s `Lock` deadlocks (Go's `sync.Mutex` is
     not reentrant): non-termination, not a counterexample.
   - A caller holding a share of the clients' view (`bView`) blocks every put `Unlock`, which
     needs the whole share, for the call's duration. So the logical view it agrees with
     (`viewAt_bView`) is the one at every commit in between.
6. **Concurrent writers between the call's `Commit` and `Begin`:**
   - Their puts reach only the write transaction and the read buffer; `D` is committed data.
   - Their commits are covered by 1.
   - bbolt switches its meta page atomically, so `Begin(false)` sees one committed state.
7. **A stopped or closing backend:** `bOpen γ qo` (above). `Close` waits for `run`'s
   `CommitAndStop` and takes `b.mu.Lock`, which `Snapshot` holds as a reader around `Begin`.
8. **The snapshot's other calls** (`Size`, `WriteTo`, `Close`: separate axioms; noted, not attacked
   in depth):
   - `Size` reads `tx.meta`, and `WriteTo` opens its own file handle; concurrent shares read only.
   - `Close` takes the whole token, so neither can follow it, and `Rollback` on an open read
     transaction returns `nil`.
   - The warning goroutine's `time.NewTicker` gets a timeout clamped from below
     (`backend.go:399-401`), so its `d <= 0` panic can't fire, even if the float-to-int conversion
     overflows.
9. **Defragmentation** (`backend.go:498`, the fork's non-blocking defrag) commits with `stop`
   mid-session and swaps `b.db` under `b.mu.Lock`. It has no spec, so no verified program calls
   it. Out of scope, as in the other reviews.
10. **Earlier verdicts:** `notes/audit.md` had no row for this axiom (added now). The OpenBackend
    review (`openbackend.md`) covers `OpenSnapshotBackend`, which consumes this snapshot's image.

## Not tried

- **No Go experiment.** Every claim reduces to bbolt's read isolation and the ordering of
  `Commit`/`Unlock`/`run`, which a test can't break without an unspecified call (defrag).
- **`boltImage`** (opaque) and `WriteTo`'s byte-level claim are not attacked.
- **What remains assumed:** the docstring's discharge argument (bbolt's `Begin(false)` isolation,
  with a read transaction begun outside the batch lock) stays an assumption about bbolt, not a proof.
