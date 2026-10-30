# backend-cmp, Review round 11 (2026-10-29): question 2's Draft (option (a), the logical view)

**Under review.** Commit `dd42add78b` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`),
diffed against `95a0c2062c`: the new module `Proof/go_etcd_io/etcd/server/v3/storage/backend/
LogicalView.lean` and the plan's section "Question 2's Draft round". `HEAD` is `dd42add78b`, so
nothing below is stale. This is the increment's first round. The statements are judged as they
will be once switched in: `spec := specF`, `batchGhostAt := batchViewQ ∗ …`, and
`viewAt := viewAtL`.

**Read.**
- The diff.
- The plan's 3.2, "After Review round 4"/"Review round 4's repairs" (R4-2), "After Review round 5"
  (R5-1, R5-2), "The user's answers to questions 2 and 4", and "Question 2: recorded".
- `InvBackend.lean`: `bViewC`/`bView` (`:202-212`), `dlNoDel`/`dlIs`/`thinV`/`thinV_refl`
  (`:492-523`), `cacheValid` (`:529`), `viewQ`/`viewQ_exact` (`:542-565`), `rtCore`/`rtRest`
  (`:602-624`), `batchGhostAt`/`batchLocked` (`:685-712`).
- `Model2.lean`: `vData`/`sData` (`:176-184`), `freeOk`/`viewSame` (`:270-288`).
- `DelKeys.lean`: `dlInit`, `dlNoDel_noDel`, `thinV_exact` (`:49-120`).
- The specs `batchTxBuffered.Unlock` (`spec`, `specC`), `UnsafeDelete` (`spec`, `specC`),
  `batchTxBuffered.commit`, `unsafeCommit`, `batchTx.Unlock` and `backend.Snapshot`, together with
  the axiom's docstring (`Proof/.../backend__Snapshot.lean:28-43`).
- `Unlock`'s proof (`batchTxBuffered__Unlock.lean`, all of it).
- `ReadSide.lean`: `rtRes_wb_close` (`:346-392`) and `rtRes_cm_close` (`:556-630`).
- `BackendBridge.lean`: `sessPuts`/`bkLockedAt`/`sData_puts` (`:139-228`),
  `batchLocked_view` (`:1715`), `bt_seqPut`, `bt_unlock0`/`bt_unlock`/`bt_unlockD`
  (`:1776-1950`), `bt_range` (`:2029`), `isKeyBackendG_of_backend` (`:2448-2523`) and
  `isKeyBackendG_of_backendC` (`:2713-2800`).
- `SnapSendBranch.lean:195-230` (`snapObs_window`).
- `backend__SetTxPostLockInsideApplyHook.lean:34-56`.
- Go at the pin (`/shared/etcd-grove/.lake/go-src/etcd/server/storage/backend/batch_tx.go`):
  - `batchTx.UnsafeDelete` (`:229-247`);
  - `batchTxBuffered.Unlock`, `commit` and `unsafeCommit`;
  - `batchTxBuffered.UnsafePut`/`UnsafeSeqPut`/`UnsafeDelete` (`:408-426`);
  - `schema/bucket.go:63,78` (`IsSafeRangeBucket`).

**Checked.**
- `etc/lean-check.py -q LogicalView.lean`: 0 errors. No `sorry`.
- `etc/importers.py --count InvBackend.lean`: 2121 modules (the plan says 2120).
- `etc/importers.py --uses batchGhostAt --uses batchLocked_view --uses viewSame --files
  InvBackend.lean`.
- No `lake build`.

## Summary

**No first-tier finding.** Each statement is true of Go, sufficient for its callers as far as I could
check by hand, and no larger than it needs to be:
- `relog`, with the agent's refinement;
- `batchViewQ` and its agreement law;
- `viewAtL`, and the `backend.Snapshot` axiom over it;
- the folded `Unlock.specF`, including a session that both puts and deletes;
- `UnsafeDelete.specC` as the final spec.

Nothing here needs the user:
- No top-level or exported statement changes.
- The only trust-base change is `viewAt`'s meaning, which is the user's option (a). It still
  needs the `axiom` skill before Freeze, as recorded.
- No new family: `specC`/`specF` disappear, and `spec_of_specF` and the no-change instance are
  corollaries of one proof.

Under the stop rule this round closes the increment's statements. The findings are all second
tier, and most are about the **plan's proof route and site list**, not about the statements:
- **R11-1:** two internal callee specs must change, and the plan does not list them:
  `batchTxBuffered.commit.spec` and `unsafeCommit.spec`.
- **R11-2:** the plan's put-branch route fails for a put session with a visible delete. The
  window has to stay exact, and the move to `relog` has to happen at the commit's close.
- **R11-3:** the old bridge cannot go through `spec_of_specF`, because its `bt_*` lemmas are shared
  with the new bridge, which has no `dlNoDel`.
- **R11-4:** the one caller `relog` exists for, the new bridge's put session, has no glue yet.
- **R11-5:** `relog`'s `P.SB` filter is now redundant.

Do R11-1 to R11-4 before the switch's first proof edit. They change what is edited, not what is
stated.

## Per target

### `relog P L st` and its laws (`LogicalView.lean:54-117`)

**Good.**
- The refinement over R4-2's sketch is right: it falls back to `L` only where the old physical view
  `vData P (st.C, st.R)` lacked the key.
  - R4-2's `sData <|> L` would undo a session's own deletes.
  - R5-1's SB-only fallback would still undo a safe-range delete of a key that is physically
    present.
  - The refinement does neither. `relog` is exactly "`L` with the session's diff applied": keys the
    session wrote take its values, keys it deleted that were physically present go, and every other
    key keeps `L`'s entry.
- `thinV_relog` (`:103`) is the law the put branch needs. It is stated over the caller-invisible
  old physical view, and it uses only the old thinness's second conjunct.
- `relog_exact` makes the `dlNoDel` corollary one line.
- It is what mvcc needs. mvcc's put sessions have `st.ndel = 0` (`sessPuts`, `BackendBridge.lean:139`),
  so `relog P vd st`'s `Key` bucket is `vd`'s bucket with the session's puts. Key by key:
  - put by the session: `sData` has it;
  - otherwise, physically present: `vd`'s value, by thinness;
  - otherwise: the fallback.

  That is `keyView (relog P vd st) (l.foldl insert m)` from `keyView vd m`, the counterpart of
  `sData_puts` (`:208`). The compacted revisions stay in mvcc's logical bucket, as R5-1 wanted.

**R11-5 (second tier; "No constant or conjunct whose reason you do not know", "After a change, drop
what existed only for what it changed").**
- **Evidence.** The `P.SB nk.1` conjunct of the filter (`:56`) came from R5-1 ("else a session's
  deletes of auth users, alarms, leases would be undone"). The refinement's
  `(vData P (st.C, st.R)).lookup nk = none` already prevents that: a key the session deleted was
  physically present.
  - What the SB conjunct still does: it drops from the logical view every *non*-safe-range key
    that `L` has and the physical view lacks. Those are registered deletable keys of other buckets.
  - That deletion is ghost-only, with no Go delete behind it.
  - For mvcc it never fires: `bridgeParams` leaves only `Key` visible, and `bkDel` registers
    `Key` keys only (`BackendBridge.lean:2418`).
- **Caller affected.** None today. A reader of the spec, though, has to ask why `relog` depends on
  `P.SB`.
- **Restatement.** `relog P L st := sData P st.S ∪ GMap.filter (fun nk _ => decide ((vData P (st.C,
  st.R)).lookup nk = none)) L`, documented as "the logical view with the session's writes and
  deletes applied". `thinV_relog` and `relog_exact` keep their proofs: drop `hc.1`.

**R11-6 (second tier, docstring).**
- **Evidence.** The header (`:9-10`) and the plan say "A key the session itself deleted is gone from
  the logical view too". That holds only for keys physically present. A put-branch session that
  deletes an already compacted key (a no-op in Go) leaves it in `relog`. This is sound, since the
  key stays thin by `dlIs`, but the sentence overclaims.
- **Restatement.** "...a key the session deleted that the readers could see is gone from it too."

### `batchViewQ γ P st` and `batchViewQ_bView` (`:124-147`), `batchLocked_thin` (`:150`)

**Good.**
- `∃ L, viewQ γ ¼ (vData P (st.C, st.R)) L` is the cheapest form, as R4-2 recommended:
  `batchLocked`'s 97 uses keep their text.
- Ghost agreement gives the clients, the readers' quarter and the batch the same `L`. So the
  deleting branch never needs to name `L`: `thinV_trans` composes the session's thinness with the
  quarter's.
- `batchViewQ_of_exact` shows today's quarter is an instance.
- `batchLocked_thin` is the backend law that replaces the bridge's `batchLocked_view`
  (`BackendBridge.lean:1715`). That lemma unfolds `batchLocked batchLockedAt batchGhost
  batchGhostAt bView bViewC` (`:1719`), backend's internals, from mvcc's package. After the switch
  it is false without `dlNoDel`, so its four uses move onto `batchLocked_thin`, and one
  cross-package unfold goes. This is a law-coverage gain to record.

No finding.

### `viewAtL γ vd` for D22's `viewAt` (`:171-189`), and `backend.Snapshot`'s axiom

**Good.**
- The definition is the user's option (a), word for word: `∃ L, ghostVar γ.view ¼ L ∗ thinV γ vd L`.
- **The axiom is only weaker as a statement.** `viewAt` occurs in the observation premise
  (`Spec/.../backend__Snapshot.lean:54`), a negative position. So with `viewAtL_of_viewAt` the
  new axiom follows from the old one.
- **The new axiom is true of Go under the new model.**
  - `Snapshot` does `b.batchTx.Commit()`, then `b.mu.RLock()` and `b.db.Begin(false)`.
  - `D` is what the last bbolt commit before `Begin` left: the call's own, the `run` goroutine's,
    or an `Unlock`'s.
  - Every such commit ends with the batch quarter at some `L` and the physical view `sData P D` thin
    of it:
    - an exact `L` today;
    - a deleting session's commit keeps `L` (`thinV_trans`);
    - a put session's commit in a window ends at `relog P vd st` (`thinV_relog`).

    So `viewAtL γ (sData P D)` holds at that point.
  - The rest of the axiom's argument (the committer holds `W ∗ Pk` at the end of the commit)
    stands. A deleting session hands over `W ∗ Pk` up front. A put session gets `W` from its wand
    at the commit's close.
- The *old* axiom would be false under the new model after a compaction, as R5-2 said. So the change
  is needed, not just allowed.
- **D22 costs nothing.**
  - `viewAt`'s only user, `snapObs_window` (`SnapSendBranch.lean:204-212`), discards it (`-`).
  - Any later user under `dlNoDel` captures that persistent fact in its `□` observation and gets
    the exact quarter back (`viewAtL_noDel`).
  - Because the plan redefines `viewAt` in place, D22's files keep their text.
- **Facts that can be combined.** An observation can combine `viewAtL` with the clients' `bView`
  inside `W` by agreement. That tells it the snapshot's data is thin of the store's logical view,
  which is what a compaction-on D22 will need.

**R11-7 (second tier, D22's file).**
- **Evidence.** The axiom's docstring (`Proof/.../backend__Snapshot.lean:37`) says "the lock's
  ghost shares were `viewAt γ (sData P C)`". After the switch it should say: the batch quarter at
  some logical view that `sData P C` is thin of.
- **Who.** This is the collaborator's file. Tell them, and put the case analysis above into
  the `axiom` skill's check: own commit, `run`'s commit, a deleting `Unlock`, and a put `Unlock`'s
  window commit.

### `Unlock.specF` (`:227-238`), `spec_of_specF` (`:242-275`), `viewSame_thin` (`:192`)

**Good. True of Go, branch by branch.** `batchTxBuffered.Unlock`: if `pending != 0`, it writes back
under `readTx.Lock`, then commits if `pending >= batchLimit || pendingDeleteOperations > 0`. The
commit runs `OnPreCommitUnsafe` under `readTx.Lock` before bbolt's commit, then resets the read
buffer.

- **The deleting branch.**
  - Its write buffer has no puts off the hook's buckets. So the write-back leaves the readers'
    view at `vData P (C, R)`, and the readers see the pre-session physical view until the commit.
  - The commit makes it `sData P S`, which the premise makes thin of the old view, and so thin of
    `L` (`thinV_trans`). The logical view and the clients' shares stay.
  - The pre-commit hook gets `Pk`. It writes only hook buckets (`Meta`), which `vData` excludes.
  - The job's `Meta` puts (`finishedCompactRev`) are in a hook bucket, so the premise allows them.
  - Safe-range keys: a deleted key may still sit in a cached read buffer (`cacheValid`). It stays
    in `L` with its value, so the cache is thin.
- **The put branch.** After `Unlock` the physical view is `sData P S`, thin of `relog P vd st`
  (`thinV_relog`). The client gets `bView γ 1 (relog …)` and makes `W ∗ Q`.
- **A session that both puts and deletes** takes the put branch and is sound. Its deletes of
  visible keys leave `relog`, and its deletes of already-compacted keys keep them, as thin keys.
  The Go window between the write-back and the commit is the existing window, with the clients'
  share deposited in `cacheInv` (see R11-2 for how the proof must treat it).
- **The disjunction is not two alternative specs.**
  - Neither branch is a layer of the other: the deleting branch holds no `bView`, and the put
    branch changes the view.
  - It is the same shape as today's `viewSame ∨ put`. The no-change sessions are an instance of the
    deleting branch (`viewSame_thin`, correct: `rw [← h.1]` then `thinV_refl`).
  - Neither side is vacuous.
- **`spec_of_specF` is correct.** It is checked: `batchLocked_thin` plus `thinV_exact`, `subst`,
  then `relog_exact`. Its put-branch witness `vData P (st.C, st.R)` is the one the old proof used.

**R11-1 (second tier, the most important: a statement change the plan does not list).**
- **Evidence.** `batchTxBuffered.commit.spec` (`Spec/.../batchTxBuffered__commit.lean:29-36`) and
  `unsafeCommit.spec` (`:30-37`) both state two things against the new design:
  - The pre requires `win = false → vData P (st.C, st.R) = sData P st.S`: out of a window, a
    commit must not change the view.
  - The window post returns `bView γ 1 (vData P (st'.C, st'.R))`, the physical view.

  `rtRes_cm_close` has the same `hview` hypothesis (`ReadSide.lean:558`).
- **Consequences.**
  - The deleting branch's commit is a non-window commit that changes the physical view, so it
    cannot call `commit` as specified.
  - The put branch's window commit must return the view at `relog P vd st`, not at the physical
    view.
- **What to draft.**
  - Out of a window, the pre should be `thinV γ (sData P st.S) (vData P (st.C, st.R))`, with
    `viewSame`'s equality as the instance.
  - In the window, the commit should take a target `L'` together with `thinV γ (sData P st.S) L'`,
    and return `bView γ 1 L'`.
- **Callers affected.** `Unlock`, `Commit`, `CommitAndStop`, `backend.run` (their proofs pass the
  equality today), and `rtRes_cm_close`.
- These are internal specs ("Scope": they may mirror the code), so the agent decides. But they are
  statement changes and their proofs, and the plan's site list and estimate leave them out.
  - The list counts "`InvCommit` 6: a commit keeps `L`".
  - It does not count `batchTxBuffered__commit`, `__unsafeCommit`, `__Commit`,
    `__CommitAndStop` or `backend__run`.

**R11-2 (second tier: the plan's proof route for the put branch fails for one case).**
- **Evidence.** The plan says "The put branch's write-back sets every quarter to `relog P vd st`,
  including the readers' quarter inside `readTx.mu`, in the write-back's close". Take a put-branch
  session that deletes a visible key `k`. After the write-back the physical view `vData P (C,
  writebackR W R)` still has `k` with its old value, because deletes are not buffered
  (`batch_tx.go:418-421`). `relog P vd st` lacks `k`. So `thinV` fails at the write-back's close.
- **Restatement of the route.** Keep today's window:
  - `rtRes_wb_close` with `win = true` sets the quarters to the exact intermediate physical view
    (no client share exists then).
  - The commit's close moves them to `relog P vd st` (R11-1's `L'`). `Unlock`'s proof keeps `vd`
    and the persistent `thinV γ (vData P (st.C, st.R)) vd` (from `batchViewQ_bView`) across the
    commit.
  - Only the no-commit put case (`win = false`, where the intermediate view is `sData P S` by
    `vData_free`) sets `relog` at the write-back's close.
- No caller has such a session today: mvcc's `sessPuts` has `ndel = 0`, and the lessor's delete is
  in a hook bucket. But `specF`'s put branch allows one, so the proof must cover it.

**R11-3 (second tier; "One spec per function" in spirit: avoid a second proof of the bridge's
lemmas).**
- **Evidence.** The plan routes "the old bridge goes through `spec_of_specF`, the new one uses
  `relog`". But the bridge's `bt_seqPut`, `bt_unlock`, `bt_range` and `bt_leaseDel` (→
  `bt_unlockD`) are each used by both bridges:
  - `isKeyBackendG_of_backend`: `:2503-2516`;
  - `isKeyBackendG_of_backendC`: `:2771-2792`, with no `dlNoDel`.
- **Consequence.** Routing the old bridge through `spec_of_specF`, whose pre has `dlNoDel`,
  needs either `dlNoDel` threaded into these shared lemmas, which breaks the new bridge, or a
  second copy of each lemma.
- **Restatement.**
  - Re-prove the four lemmas once, over `batchLocked_thin` and `relog`. They need no `dlNoDel`,
    and both bridges use them.
  - `bt_range` already has the `Del k` disjunct for this (`bkDel = dlIs` at `Key`, `:2418`).
  - `spec_of_specF` then has no caller. Keep it only as the documented proof that today's spec is
    an instance, or drop it ("After a change, drop what existed only for what it changed").
  - Its docstring calls it "Today's `spec`", but its pre adds `dlNoDel γ`. Name it for what it
    is: `spec_noDel_of_specF`.
- **Still to add (the plan has it).** The no-change corollary without `dlNoDel`, for `bt_unlock0`,
  `bt_unlockO`, `bt_unlockOAt` and `SetTxPostLockInsideApplyHook` (`:56`). It is one line through
  `viewSame_thin`.

**R11-4 (second tier; the Draft step: "prove the glue of every caller").**
- **Evidence.** The only glue proved in this round is the `dlNoDel` corollary. The caller that
  `relog` exists for is the new bridge's put session: `bt_unlock` with `bkView γ 1 (l.foldl insert
  m)` from `bView γ 1 (relog P vd st)`. It is not written.
- **Restatement.** It can be written now, against `specF` as a hypothesis, before any switch. It
  needs:
  - `batchLocked_thin` (exists);
  - a `sData_puts` counterpart, `keyView vd m → thinV-pure (vData P (st.C, st.R)) vd →
    sessPuts P st l → keyView (relog P vd st) (l.foldl insert m)`, by `relog_lookup` (about 30
    lines).

  By my hand check above this goes through, so I rate the statement complete. Writing the glue is
  the check of record, and it costs less than a review round.

### `UnsafeDelete.specC` as the final `UnsafeDelete.spec`

**Good.**
- It is true of Go: `batchTx.UnsafeDelete` deletes in bbolt's writer and counts a pending
  operation, and `batchTxBuffered.UnsafeDelete` adds a pending delete and does not touch the
  buffer.
- The `dlIs` premise at a safe-range key is what the readers' thinness needs. The old spec's
  `P.SB bi.name = false` becomes the `if`.
- Today's spec is the instance `own := true`, `P.SB = false`. Its one direct caller, `bt_leaseDel`,
  deletes from `Lease`, which is not safe-range. The other holders only pass the hypothesis
  through:
  - `StoreBackend`;
  - `BuildLemmas`;
  - `SnapApplyWalk`;
  - `EtcdServer.applySnapshot`;
  - `NewServer`.
- The `own` flag is a case split on how the key argument is held: a caller's slice, or a slice
  into the transaction (`txBytes st.tx`, as the compaction's `UnsafeRange`-then-`UnsafeDelete`
  loop has it). It is not a disjunction of specs, and the same form comes back in the post.

No finding.

## The plan's proof sites and estimate

- **Credible for the backend files.** Counts of the quarter's mentions, by grep:

  | file | plan | grep |
  |---|---|---|
  | `InvBatch` | 16 | 18 |
  | `ReadSide` | 8 | 6 |
  | `InvCommit` | 6 | 6 |
  | `NewAlloc` | 3 | 3 |
  | `InvSnapshot` | 2 | 2 |
  | `batchTx__lock` | 2 | 2 |

  The 2120-module rebuild is right (2121).
- **Missing:**
  - R11-1's specs and proofs: `commit`, `unsafeCommit`, and the callers `Commit`,
    `CommitAndStop` and `run`.
  - `rtRes_cm_close`'s window target.
  - In the bridge: `batchLocked_view` (`:1715`) and its four uses. Two of them, `bt_seqPut`
    (`:1804`) and `bt_range` (`:2057`), are not `Unlock` callers, but they read the batch quarter
    and are shared with the new bridge (R11-3).
- **Estimate.**
  - The bridge's "about 60" is low. Rewriting `bt_seqPut`, `bt_range`, `bt_unlock` and
    `bt_unlockD` over the thin view, plus the `relog` lemma, is more like 150-250 lines.
  - Add about 100-150 lines for the commit specs and their four callers.
  - The order of magnitude (well under 2k lines, one full build per round) holds.

## Does anything need the user?

No:
- **Top-level statements.** None change. `Unlock.spec` and `UnsafeDelete.spec` reach the server
  and the links only as hypotheses passed through.
- **The trust base.** `viewAt`'s meaning is the user's option (a). The `axiom` skill run on
  `backend.Snapshot` before Freeze is already recorded (add R11-7's cases to it). The collaborator
  should hear that the axiom's docstring changes.
- **Families.** `specC` and `specF` go at the switch. `spec_of_specF` and the no-change instance
  are corollaries of the one proof. Under R11-3, the bridge keeps one copy of each lemma.

## Stop rule and ranking

This is the increment's first round and it has no first-tier finding, so the increment's
statements are reviewed. The next round is for whatever the switch changes beyond these drafts.
That means R11-1's commit specs, which are internal: a review is optional, but cheap if they turn
out non-mechanical.

Ranked by need of revision. All second tier.
1. **`Unlock.specF`'s route and corollaries.** R11-1 (the commit specs), R11-2 (the window),
   R11-3 (the shared bridge lemmas and `spec_of_specF`'s name and use), R11-4 (the missing glue).
   The statement itself stands.
2. **The plan's site list and estimate.** The omissions above.
3. **`relog`.** R11-5 (drop `P.SB`) and R11-6 (the docstring).
4. **`viewAtL` and the `Snapshot` axiom.** R11-7 (the docstring, the axiom check's cases).
5. **`batchViewQ`.** No finding.
6. **`UnsafeDelete.specC`.** No finding.

No bug in the Go code was found; nothing for `issues/`.
