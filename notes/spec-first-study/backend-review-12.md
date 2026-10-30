# backend-cmp, Review round 12 (2026-10-29): question 2's switch

**Under review.** Commit `f175d283b5` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`),
diffed against `adfd06e232`. It implements the Draft that round 11 reviewed
(`backend-review-11.md`), with round 11's findings R11-1 to R11-7 applied (plan, "Question 2's
switch"). `HEAD` is `f175d283b5`, so nothing below is stale. This is the increment's **second**
round.

**Read.**
- The whole Lean diff.
- `InvBackend.lean`:
  - `relog`, `relog_lookup`, `relog_exact`, `relog_same` (`:195-231`);
  - `bView`/`bViewC` (`:248-261`), `cacheInv` (`:428`);
  - `dlIs`/`thinV`/`thinV_refl` (`:548-571`), `cacheValid` (`:575`), `viewQ` (`:588`);
  - `rtCore`/`rtRest`/`rtRes` (`:648-681`);
  - `batchViewQ`/`batchGhostAt`/`batchLocked` (`:726-766`);
  - `thinV_trans`, `thinV_relog`, `batchViewQ_of_exact`, `batchViewQ_bView`, `batchLocked_thin`,
    `viewSame_thin` (`:769-845`).
- `InvSnapshot.lean:126-135` (`viewAt`). `DelKeys.lean:106` (`thinV_exact`).
- The specs `batchTxBuffered.Unlock`, `UnsafeDelete`, `commit`, `unsafeCommit`, and
  `backend.Snapshot` (spec, and the axiom's docstring).
- The proofs of `Unlock`, `UnsafeDelete`, `commit`, `unsafeCommit`, `Commit`, `CommitAndStop`,
  `run` and `SetTxPostLockInsideApplyHook`.
- `ReadSide.lean`: `rtRes_wb_close` (`:343-400`), `rtRes_wb_close_same` (`:411`) and
  `rtRes_cm_close` (`:568-720`).
- `InvCommit.lean` (`commit_ghost`, `batchLockedW_setHw`) and `InvBatch.lean` (`batchGhostW`).
- `BackendBridge.lean`:
  - `keyView_sub`/`keyView_relog` (`:228-286`);
  - `bt_seqPut` (`:1821`), `bt_unlock` (`:1915`), `bt_unlockD` (`:1954`), `bt_leaseDel`;
  - `bt_range` (`:2084`), `bt_unlockO` (`:2338`), `keyView_thin` (`:2648`);
  - the two `isKeyBackendG_of_backend*`.
- The deleted `LogicalView.lean` (at `adfd06e232`), symbol by symbol.
- Go at the pin, `/shared/etcd-grove/.lake/go-src/etcd/server/storage/backend/`:
  - `batch_tx.go`: `batchTx.UnsafeDelete` (`:229-247`), `batchTxBuffered.UnsafeDelete`
    (`:418-421`), `Unlock`, `commit`, `unsafeCommit`;
  - `backend.go`: `Snapshot`, `run`.

**Checked.**
- The build log the brief names: `Build completed successfully`, exit 0.
- The diff adds no `sorry` and no `axiom`.
- `etc/api/` lists only raft, so the backend has no generated interface to diff.
- No build of my own.

## Summary

**One first-tier finding, R12-1 ("No unneeded premise").**
- `UnsafeDelete.spec`'s new `dlIs` premise at a safe-range key is dropped by its own proof
  (`wp_start … -⟩`) and carried by nothing after it.
- The registration the readers' thinness needs enters at `Unlock`'s deleting branch (`thinV`), not
  at the delete.
- The defect was latent in round 11's Draft. Round 11 rated `specC` "good: the `dlIs` premise is
  what the readers' thinness needs", but `specF`'s deleting branch already asked for that thinness
  itself.
- So this is **not churn** from round 11's repairs, and the repair is mechanical.

Everything else holds:
- The statements are true of Go.
- The callers' instances are right.
- Nothing finished was lost.
- Nothing needs the user.

The second-tier findings:
- **R12-2:** four new cross-package `iunfold thinV` and one `unfold relog` in the bridge, which are
  missing backend laws. This is the one cost R11-3's repair brought.
- **R12-3:** `viewAt` has no law. `viewAtL_noDel` was dropped, and the "agrees with the clients'
  shares" that the header promises is not a law.
- **R12-4:** `keyView_sub` duplicates the first half of `keyView_thin`.
- **R12-5:** stale docstrings (`rtRes_cm_close`, the `Snapshot` spec's header).
- **R12-6:** `L'` is a dead parameter out of a window. A note only.

## Per target

### `batchViewQ`, `batchGhostAt`/`batchGhostW` (`InvBackend.lean:726-746`, `InvBatch.lean:427`)

**Good.**
- Both first conjuncts are `batchViewQ γ P st`, as drafted.
- The 16-odd step lemmas only add `batchViewQ` to their `unfold` lists. The session steps keep
  `(C, R)`, so `L` is carried through untouched.
- `commit_ghost` takes the new quarter as a `viewQ … L` for a caller-chosen `L` and re-packs it.
- `NewAlloc` starts exact (`batchViewQ_of_exact`).

No finding.

### `viewAt` and the `backend.Snapshot` axiom (`InvSnapshot.lean:133`, `Spec/.../backend__Snapshot.lean`)

**Good.**
- `viewAt γ vd := ∃ L, viewQ γ ¼ vd L` is option (a) exactly.
- **The axiom is weaker as a statement.** `viewAt` occurs only as an antecedent of the caller's
  observation (`Spec/...:54`). The old `viewAt` implies the new one (`viewQ_exact`), so the new
  observation premise implies the old, and the old axiom implies the new.
- **True of Go under the model.** The axiom's argument is "the last bbolt commit before
  `Begin(false)` left the lock's quarter at `viewAt γ (sData P C)`". It now holds at every commit's
  close: `unsafeCommit.spec`'s post gives `batchGhostAt γ P st' true` with
  `vData P (st'.C, st'.R) = sData P st.S`, and `batchViewQ` is then exactly
  `viewAt γ (sData P C)`. There are four kinds of commit:
  - `Commit`'s, `run`'s and `CommitAndStop`'s: exact (`thinV_refl`);
  - a deleting `Unlock`'s: `L` kept, the new physical view thin of it by `thinV_trans`
    (`ReadSide.lean`, `rtRes_cm_close`, the `win = false` branch);
  - a put `Unlock`'s window commit: `L' = relog P vd st`, with `thinV_relog`.

  In the last case the committer holds `W` only after applying its wand to the returned
  `bView γ 1 L'`. That is a ghost step at the same point, so the argument stands, but the
  `axiom` skill's check should state it (R11-7's case list).
- **D22 is unaffected.** `snapObs_window` discards `viewAt` (`SnapSendBranch.lean:209`).

The trust base changes only by the user's option (a). The `axiom` skill before Freeze is
recorded.

See R12-3 (no laws) and R12-5 (the spec header).

### `commit.spec` / `unsafeCommit.spec` (R11-1)

**Good.**
- **Out of a window**, the pre is `thinV γ (sData P st.S) (vData P (st.C, st.R))`. This is what
  Go allows: `unsafeCommit` runs under `readTx.Lock` and resets the read buffer, so a commit that
  drops keys is seen by the readers only after it. The proof composes it with the quarter's
  thinness (`thinV_trans`), and `cacheValid` with `thinV_rebase`.
- **In a window**, the pre is `thinV γ (sData P st.S) L'` and the post is `bView γ 1 L'`. All
  three quarters are collected at `rtRes_cm_close`: the clients' quarter in `cacheInv`, the
  batch's, and the readers' under `readTx.mu` held whole. So moving the logical view to any `L'`
  the new physical view is thin of is a sound ghost update. Cached states at the window's version
  are poisoned (`hwin0`), so `cacheValid` needs only `Hpre`.
- **Commit, CommitAndStop and run** pass `win = false` and `L' := vData P (st.C, st.R)`. The
  premise follows by `vData_free` and then `thinV_refl` (`batchTxBuffered__Commit.lean:49-57`,
  `__CommitAndStop.lean:47-56`, `backend__run.lean:95-104`). That is right: a free state's
  physical view is the writer's contents.
- **`Unlock`** passes:
  - deleting branch: `win = false`, with the caller's `Hth` rewritten by `hsame`
    (`batchTxBuffered__Unlock.lean:197-206`);
  - put branch that commits: `win = true`, `L' := relog P vd st`, from
    `thinV_relog … Hthvd` (`:247-260`).

**R12-6 (note, not a finding).**
- **Evidence.** Out of a window, `L'` appears nowhere, and the callers fill it with
  `vData P (st.C, st.R)`. That is harmless for an internal spec, but a reader may wonder what it
  means.
- **Restatement.** Optional: one docstring phrase, "(`L'` unused out of a window)".

### `rtRes_cm_close`, `rtRes_wb_close` (`ReadSide.lean:348`, `:573`)

**Good.**
- `rtRes_wb_close` opens the window at the exact intermediate view. Only `win = false` moves the
  view to `L'`, with `thinV (vData P (C, writebackR W R)) L'`. That is R11-2's route. It is
  correct because the deletes are not buffered (`batch_tx.go:418-421`), so the intermediate view
  still has the session's deleted keys.
- In `rtRes_cm_close`, the batch's and the readers' quarters agree (`hL : Lb = L`), which replaces
  the old "the quarter is exact" step. Out of a window both keep `Lb`; in a window both go to `L'`.

R12-5: the docstring is stale.

### `Unlock.spec`, folded (`Spec/.../batchTxBuffered__Unlock.lean:48`)

**Good. The statement is round 11's `specF`, and its proof covers every Go path.**
- **`pending == 0`:**
  - deleting branch: nothing happens;
  - put branch: `relog_same` (the physical view is the writer's contents, and is included in
    `vd` by `batchViewQ_bView`) gives back `bView γ 1 vd`.
- **`pending != 0`, deleting branch:**
  - The write-back leaves the readers' view (`rtRes_wb_close_same`, `hsame` from no non-hook
    puts).
  - The commit, if `limit ≤ pend ∨ ndel > 0`, gets the caller's thinness.
  - Otherwise there is no commit: `ndel = 0`, so the session made no deletes, and `freeOk`
    holds.
- **`pending != 0`, put branch:**
  - With a commit: the window opens exact and the commit's close moves it to `relog` (R11-2).
  - Without a commit (`ndel = 0`): the write-back's close goes to `relog`. There the intermediate
    view is `sData P st.S` (`hvf`, `vData_free`).
- This matches Go's `Unlock`: write-back under `readTx.Lock`, then `commit(false)` under the same
  test.
- **No family.**
  - `spec`, `specC`, `specF` and `spec_of_specF` are one statement now.
  - The no-change instance is `viewSame_thin` at each call site: `bt_unlock0`, `bt_unlockD`,
    `bt_unlockO`, `SetTxPostLockInsideApplyHook`.
- **Callers.** Under `dlNoDel` (the old bridge, D22) `relog P vd st` is `sData P st.S`
  (`thinV_exact`, then `relog_exact`). So no caller lost anything. The put branch's post is now
  what is true with compaction.

Minor glue cost: `bt_unlockO` spends 6 lines on the no-change branch (`BackendBridge.lean:2359-2367`),
where it used to spend 1. A corollary `viewSame P st → W ∗ Pk ∗ Q ⊢ <the deleting disjunct>` would
make every no-change caller one line again. This is optional.

### `UnsafeDelete.spec` (`Spec/.../batchTxBuffered__UnsafeDelete.lean:36`)

**Good.**
- It is true of Go: `batchTx.UnsafeDelete` deletes in bbolt's writer and does `pending++`, and the
  buffered wrapper does `pendingDeleteOperations++` and does not touch the buffer. Neither
  depends on the bucket kind.
- `sessWf_del` no longer needs "not safe-range", because `safeSt` has lost clause 3. Its new
  proof is `⟨hsf.1, …⟩`, so nothing about the writer's contents is used.
- `own` is a case split on how the key is held, not a disjunction of specs.
- `bt_leaseDel` instantiates `own := true` and a `P.SB = false` bucket (`BackendBridge.lean:2053`).

**R12-1 (first tier: "No unneeded premise").**
- **Evidence.** The premise `(if P.SB bi.name then dlIs γ (bi.name, kb) else True)` (`:43`) is
  discarded by the proof's `wp_start … Hrbp, -⟩` (`Proof/.../batchTxBuffered__UnsafeDelete.lean:33`).
  The post `batchLocked γ P b (st.del bi kb)` records nothing of it: `batchLocked` has no record
  of registered deletes.
- **No later step uses it either.**
  - `Unlock`'s deleting branch takes the whole `thinV γ (sData P st.S) (vData P (st.C, st.R))`
    from its caller again, `dlIs` of every dropped key included.
  - The put branch needs no registration for a visible key it deletes, because `relog` drops it.
- So the premise is neither needed by the code nor bought back by a stronger result.
- The docstring's reason, "a key registered as deletable …, which the readers then may miss", is
  false of this design. The readers miss the key because of `Unlock`'s premise.
- **Caller affected.**
  - Today: `bt_leaseDel` only (`P.SB = false`, so the premise is `True`); no harm.
  - Later: the compaction job (the new bridge's limited-range `sorry`) would prove `dlIs` twice,
    once at each `UnsafeDelete` and again, for the same keys, inside `Unlock`'s `thinV`.
- **Restatement. Pick one.**
  - **(a) Drop the conjunct**, and the docstring sentence with it. This is the smallest repair:
    the spec gets strictly stronger, and the job's session token records the registration, as the
    plan's "Left" already says.
  - **(b) Make the premise pay.**
    - Keep it, and have the session carry a persistent record:
      `□ ∀ nk, ⌜P.SB nk.1 ∧ (vData P (st.C, st.R)).lookup nk ≠ none ∧ (sData P st.S).lookup nk = none⌝ -∗ dlIs γ nk`,
      kept by every session step and set by `UnsafeDelete`.
    - `Unlock`'s deleting branch then drops the `dlIs` half of `thinV` for safe-range keys.
    - It keeps the pure inclusion, and `dlIs` for visible keys outside the safe-range buckets
      (none under `bridgeParams`).
    - The job then needs no record in mvcc's token, but `batchLocked` grows a conjunct.

  I recommend (a) now. Let the limited-range glue decide whether (b) is cheaper, and if it is,
  bring the premise back together with the post that uses it.

### `relog`, `relog_same` (R11-5, R11-6; `InvBackend.lean:195-231`)

**Good.**
- The `P.SB` filter is gone. `thinV_relog` and `relog_exact` kept their proofs.
- The docstring now says "if the readers could see it" (R11-6).
- `relog_same` is the right law for the put branch's `pending == 0` case. It takes exactly the
  pure half of `batchViewQ_bView`'s thinness.

No finding.

### The bridge (`BackendBridge.lean`): shared `bt_*` over thin views, `keyView_sub`/`keyView_relog`, `bt_range`'s new premise

**Good.**
- R11-3 is done as recommended. `bt_seqPut`, `bt_unlock`, `bt_unlockD` and `bt_range` are proved
  once over `batchLocked_thin` and serve both bridges. `batchLocked_view` (`adfd06e232:1715`,
  which unfolded six backend definitions) is gone.
- `keyView_relog` (R11-4) is the glue `relog` exists for. It is the `sData_puts` counterpart
  round 11 sketched.
- `bt_unlockD`'s Lease delete is in a hook bucket, so `relog P vd (st0.del bi k) = relog P vd st0`.
- **`bt_range`'s new premise `□ (∀ k, dlIs γ (key, k) -∗ Del k)`** is the right shape. The
  range's right disjunct is now reachable: a key in the logical bucket `m` that the physical view
  lacks and the session did not put. Each bridge meets the premise with what it already holds:
  - the old bridge: by `dlNoDel_noDel` (`exfalso`, 3 lines, `:2609-2611`);
  - the new bridge: `bkDel` is `dlIs` at `Key` (`:2880-2882`).

  No statement above `bt_range` changes: `isKeyBackendG_of_backend*` keep their text.

**R12-2 (second tier: "A client does not unfold … any other package's definitions"; the cost of
R11-3's repair).**
- **Evidence.** The repair adds backend unfolds to mvcc's file:
  - `iunfold thinV at Hth` at `:1849`, `:1936`, `:1985` and `:2114`. Each takes either the pure
    inclusion only, or the inclusion together with the `dlIs` clause (`:2116`);
  - `unfold relog` with a `show` of its body at `:1999`.

  These sit beside the pre-existing `iunfold backend.thinV` in `keyView_thin` (`:2653`). The net
  effect against round 11's gain (one six-definition unfold gone) is still positive, but these
  are missing laws.
- **Restatement.** Add to `InvBackend.lean`:
  - `thinV_sub : thinV γ vd L ⊢ ⌜∀ nk v, vd.lookup nk = some v → L.lookup nk = some v⌝`;
  - `thinV_dl : thinV γ vd L ⊢ □ ∀ nk, ⌜L.lookup nk ≠ none ∧ vd.lookup nk = none⌝ -∗ dlIs γ nk`;
  - `relog_congr : sData P st.S = sData P st'.S → st.C = st'.C → st.R = st'.R → relog P L st = relog P L st'`,
    or `relog_del_HB` directly.

  Then the five sites become `ihave`s.

**R12-4 (second tier: duplication).**
- **Evidence.** `keyView_sub`'s body (`:231-254`) is, almost word for word, the first `isplitr`
  branch of `keyView_thin` (`:2659-2680`), which builds the same filtered bucket.
- **Restatement.** Prove `keyView_thin`'s first conjunct by `keyView_sub` (with `thinV_sub` from
  R12-2).

### What was deleted: superseded or lost?

| at `adfd06e232` | at `HEAD` |
|---|---|
| `LogicalView.relog`, `relog_lookup`, `relog_exact`, `thinV_trans`, `thinV_relog` | `InvBackend.lean`, unchanged but for R11-5 |
| `batchViewQ`, `batchViewQ_of_exact`, `batchViewQ_bView`, `batchLocked_thin` | `InvBackend.lean` |
| `viewSame_thin` | `InvBackend.lean`, used at 5 sites |
| `viewAtL` | became `viewAt` (`InvSnapshot.lean:133`) |
| `viewAtL_of_viewAt` | moot: the old `viewAt` no longer exists, and its content is `viewQ_exact` |
| `viewAtL_noDel` | **dropped, with no user** (R12-3) |
| `Unlock.specC`/`specF`/`spec_of_specF` | `Unlock.spec`; `spec_of_specF` had no caller after R11-3 |
| `UnsafeDelete.specC` | `UnsafeDelete.spec` |
| `batchLocked_view` (bridge) | `batchLocked_thin` + `keyView_sub` |

Nothing finished got weaker:
- No linked result, `Results.lean` or `Link.lean` changed.
- `Unlock.spec` and `UnsafeDelete.spec` reach the server only as hypotheses passed through.
- The one weakened trusted statement is the `Snapshot` axiom, by option (a).

**R12-3 (second tier: "Law coverage"; "Facts that can be combined").**
- **Evidence.**
  - `viewAt` now has no law at all.
  - Its header (`InvSnapshot.lean:36-39`) says it "agrees with the clients' shares (`bView`) …,
    the physical view thin of theirs". Round 11 counted on that agreement, and on `viewAtL_noDel`,
    for D22's future users ("D22 costs nothing").
  - Before the switch, `viewAt` was a bare `ghostVar` that a client could `icombine`. Now a client
    would have to unfold `viewAt`, `viewQ` and `bView`.
- **Caller affected.** None today (`snapObs_window` discards it). It matters for any D22
  observation that uses it, which belongs to the collaborator.
- **Restatement.** Add next to `viewAt`, both short, by the proofs of `batchViewQ_bView` and
  `thinV_exact`:
  - `viewAt_bView : viewAt γ vd ∗ bView γ q vd' ⊢ viewAt γ vd ∗ bView γ q vd' ∗ thinV γ vd vd'`;
  - `viewAt_noDel : dlNoDel γ ∗ viewAt γ vd ⊢ ghostVar γ.view ¼ vd`, or
    `⊢ … ∗ ⌜∀ vd', bView … vd' → vd' = vd⌝`. Alternatively drop the header's promise.

### R12-5 (second tier: stale docstrings)

- **`rtRes_cm_close`** (`ReadSide.lean:568-572`) still ends "Not in a window, the view must be
  unchanged". It should say: out of a window, the logical view is kept and the new physical view
  is thin of the old; in a window, the view moves to `L'`.
- **`Spec/.../backend__Snapshot.lean`'s header**, lines 12-17, still reads `viewAt` as "the batch
  lock's quarter of the readers' view at `vd`", and "`D` reads as the readers' view". After the
  switch, `D` reads *thin of* it. R11-7 updated only the axiom's docstring in the `Proof/` file.
  This is D22's file, so tell the collaborator.

## Does anything need the user?

No.
- **Top-level or exported statements:** none changed. The diff touches no `Link`/`Results`, and
  `isKeyBackendG_of_backend*` keep their statements.
- **The trust base:** changes only by `viewAt`'s meaning, option (a). The `axiom` skill is still
  due before Freeze; add R11-7's four commit cases, with the put window's "`W` from the wand at
  the commit's close".
- **New families:** none. `specC`, `specF` and `spec_of_specF` are gone, and the no-change case
  is an instance.
- R12-1's option (b) would add a conjunct to `batchLocked`, an internal predicate. That is still
  the agent's call.

## Stop rule

- This is the increment's second round, with one first-tier finding.
- **R12-1 does not come from round 11's repairs.** It was in the Draft that round 11 passed. So
  there is no churn of the first tier.
- The churn that round 11's repairs did bring is second tier (R12-2, R12-4), the price of sharing
  the bridge lemmas: unfolds and one duplicated proof.
- Repair R12-1 (option (a) is a 3-line edit plus the docstring) and review once more as the
  increment's third round. If that round finds a first-tier problem in the same statements, the
  plan's rule sends it to the user, or to the limited-range glue.

## Ranked by need of revision

1. **`UnsafeDelete.spec`**, first tier: R12-1, the unused `dlIs` premise.
2. **The bridge's shared lemmas**, second tier: R12-2 (backend laws `thinV_sub`/`thinV_dl`/
   `relog_congr` in place of five unfolds), and R12-4 (`keyView_sub` against `keyView_thin`).
3. **`viewAt`**, second tier: R12-3 (no laws; `viewAtL_noDel` dropped), and R12-5 (the `Snapshot`
   spec's header).
4. **`rtRes_cm_close`**, second tier: R12-5's stale docstring.
5. **`Unlock.spec`**: no finding. An optional no-change corollary would save glue in `bt_unlockO`.
6. **`commit.spec`/`unsafeCommit.spec`**: no finding (R12-6 is a note).
7. **`relog`/`relog_same`, `batchViewQ`/`batchGhostAt`/`batchGhostW`**: no finding.

No bug in the Go code was found; nothing for `issues/`.
