# backend-cmp, Review round 13 (2026-10-29): round 12's repairs

**Under review.** Commit `c312203e9d` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`),
diffed against `f175d283b5` (the switch, reviewed in `backend-review-12.md`). `HEAD` is
`c312203e9d`, so nothing below is stale. This is the **third** round of question 2's increment.

**Read.**
- The whole Lean diff (7 files, +75/-51) and the plan's new section ("Review round 12 and its
  repairs").
- `InvBackend.lean`:
  - `relog`/`relog_lookup`/`relog_exact`/`relog_congr`/`relog_same` (`:195-237`);
  - `bViewC`/`bView` (`:254-264`), `dlNoDel`/`dlIs`/`thinV`/`thinV_refl` (`:544-575`);
  - `viewQ`/`viewQ_exact` (`:594-617`), `batchViewQ` (`:732`), `batchGhostAt`, `batchLocked`;
  - `thinV_sub`/`thinV_dl` (`:773-786`), `thinV_trans`, `thinV_relog`, `batchViewQ_of_exact`,
    `batchViewQ_bView` (`:829`), `batchLocked_thin`, `viewSame_thin`.
- `DelKeys.lean`: its imports and declarations, `thinV_exact` (`:106`).
- `InvSnapshot.lean`: the header (`:35-39`), `viewAt` (`:134`), `viewAt_bView`, `viewAt_noDel`
  (`:137-158`).
- `ReadSide.lean`: the header (`:19-25`), `rtRes_cm_close` (statement, `:569-596`).
- The specs `UnsafeDelete` (whole file), `Unlock`, `unsafeCommit` and `backend.Snapshot` (whole
  file); the proof of `UnsafeDelete`.
- `BackendBridge.lean`: `keyView_sub` (`:231`), `bt_seqPut` (`:1849`), `bt_unlock` (`:1935`),
  `bt_unlockD` (`:1983-1998`), `bt_leaseDel` (`:2005-2070`), `bt_range` (`:2109`), `keyView_thin`
  (`:2639-2680`); every remaining `unfold`/`iunfold` in the file (tallied).
- `notes/backend-cmp-plan.md`: the "Out" scope (`:28-36`) and section 5, "Overlap with D22".
- Go at the pin, `/shared/etcd-grove/.lake/go-src/etcd/server/storage/backend/batch_tx.go`:
  `batchTx.UnsafeDelete` (`:229-247`), `batchTxBuffered.UnsafeDelete` (`:418-421`),
  `batchTxBuffered.Unlock` (`:328-`).

**Checked.**
- The build log the brief names ends `Build completed successfully (10945 jobs)`, exit 0. Its
  warnings on the touched files are the old deprecations (`if_true`, `if_neg`) and unused simp
  arguments, all from replayed modules.
- The diff adds no `sorry` and no `axiom`.
- No statement changed except `UnsafeDelete.spec` (one conjunct fewer). The new laws are additions.
  No `Link`/`Results` file was touched.
- No build of my own.

## Summary

**No first-tier finding.** Every round-12 finding is repaired as recommended:

| R12 | Repair at `c312203e9d` | Verdict |
|---|---|---|
| R12-1 | `UnsafeDelete.spec`'s `dlIs` conjunct and its docstring sentence dropped; the proof's `-` pattern gone; `bt_leaseDel` simplifies with `↓reduceIte` only | done |
| R12-2 | `thinV_sub`, `thinV_dl`, `relog_congr`; the five bridge sites and `keyView_thin` use them | done (no `thinV`/`relog` unfold left in mvcc) |
| R12-3 | `viewAt_bView`, `viewAt_noDel`; `InvSnapshot` imports `DelKeys` | done; see R13-2 |
| R12-4 | `keyView_thin`'s first half is `keyView_sub hv Hsub` (23 lines gone) | done |
| R12-5 | `rtRes_cm_close`'s docstring, `ReadSide.lean`'s header, the `Snapshot` spec's header | done, and accurate against the statements |
| R12-6 | a note; left as it was | fine (the `unsafeCommit` docstring already explains `L'`) |

**Churn: none of the first tier.** The repairs leave three small things, all second tier or notes:
- **R13-1:** a dead `have hSB` in `bt_leaseDel`.
- **R13-2:** `viewAt_bView` is `batchViewQ_bView` again, because `viewAt` and `batchViewQ` are one
  definition written twice.
- **R13-3:** a stale `DelKeys` import in the `UnsafeDelete` spec file. This one predates the repair.

**The increment's statements, re-checked briefly:** still no first-tier finding.
- `batchViewQ`, `viewAt`, the commit and `unsafeCommit` specs, `Unlock.spec` and `relog` are
  textually unchanged since round 12. Round 12 found them true of Go and complete for their callers.
- `UnsafeDelete.spec` only got stronger.
- The shared bridge lemmas changed proofs only.

**Stop rule.** This is the increment's third round, and the same statements draw **no** first-tier
finding. The increment has converged. Stop reviewing it, and move to:
- the limited-range glue (the new bridge's `sorry`), where option (b) of R12-1 may come back with a
  post that uses it;
- the `axiom` skill on `backend.Snapshot` before Freeze, as the plan already records.

**Does anything need the user? No.**
- No top-level or exported statement changed.
- The trust base is unchanged since round 12 (option (a) was the user's).
- No family was added.
- One thing for the collaborator, not the user: the `Snapshot` spec's header (D22's file) now
  reads `D` as thin of the logical view. STATUS records this.

No bug in the Go code was found; nothing for `issues/`.

## Per target

### `UnsafeDelete.spec` (R12-1)

**Good.**
- The premise is now `isPkgInit ∗ isBackend ∗ batchTx ↦□ ∗ batchLocked ∗ isBucket ∗ key ∗ rbPut`
  (`Spec/.../batchTxBuffered__UnsafeDelete.lean:41-44`). Every conjunct is used:
  - `isBucket` and the key are passed to `batchTx.UnsafeDelete`;
  - `rbPut` goes to `batchGhost_step_rb`.
- The pure premises are each needed:
  - `P.has bi` for the bucket;
  - the `pend` bound for `pending++`;
  - `P.hk … = false`, because the hook's own keys are not deletable through this path
    (`hkData_del`).
- **True of Go.** `batchTx.UnsafeDelete` deletes in bbolt's writer (a missing bucket is
  `lg.Fatal`, excluded by `isBucket`) and does `t.pending++` (`batch_tx.go:229-247`). The
  buffered wrapper adds `pendingDeleteOperations++` and does not touch `t.buf`
  (`batch_tx.go:418-421`). The post `batchLocked … (st.del bi kb)` says exactly that.
- **Strictly stronger than at `f175d283b5`.** The proof is unchanged apart from the pattern
  (`Proof/.../batchTxBuffered__UnsafeDelete.lean:33`).
- **The docstring now places the readers' thinness where it is paid:** `Unlock`'s deleting
  branch, `thinV`. It records the dropped premise in its history clause.
- **The caller.** `bt_leaseDel` (`BackendBridge.lean:2048-2049`) instantiates `own := true` and
  reduces the `if own` with `↓reduceIte` alone. The `P.SB` rewrite is gone with the conjunct.
- **The plan's "Left"** (`backend-cmp-plan.md:1230-1231`) already puts the registration in the
  job's session token for `Unlock`'s `thinV`. So the compaction job will prove `dlIs` once.

**R13-1 (note: dead code left by the repair).**
- **Evidence.** `have hSB : P.SB leaseBI.name = false := by rw [hP.2.2.2.1]; decide`
  (`BackendBridge.lean:2037`) was used only by the removed `simp only [… hSB …] at hDel'`. It now
  has no use in `bt_leaseDel` (checked: the one occurrence in `:2005-2078`). The build reports no
  unused-variable warning for it, which is why it survived.
- **Caller affected.** None; this is proof hygiene.
- **Restatement.** Delete the line.

**R13-3 (note: a stale import, not churn).**
- **Evidence.** The spec file publicly imports `…backend.DelKeys` (`:10`). The statement uses
  nothing of it: `dlIs` and `thinV` are in `InvBackend` (`:554`, `:563`), `txBytes` in
  `InvBbolt`. The import was already there at `f175d283b5` and `adfd06e232`, so the repair did not
  introduce it. But with `dlIs` gone the file has no reason to name `DelKeys` at all.
- **Restatement.** Drop the import if the file builds without it. Otherwise ignore this.

### The new laws `thinV_sub`, `thinV_dl`, `relog_congr` (R12-2)

**Good.**
- **`thinV_sub` and `thinV_dl` are exactly `thinV`'s two conjuncts**, as round 12 stated them
  (`InvBackend.lean:773-786`). Together they are equivalent to `thinV`: both projections, and
  `thinV` is persistent. So a client never needs the definition again.
- **`relog_congr`** (`:219-223`) is the congruence round 12 asked for. Its premises are what
  `relog` reads: `sData P st.S`, `st.C`, `st.R`.
- **The bridge** (`BackendBridge.lean:1849`, `:1935`, `:1983`, `:2109-2110`, `:1995-1996`,
  `:2648-2649`) uses each law in one line. The tally of the file's `unfold`/`iunfold` shows no
  `thinV`, `relog`, `viewQ`, `batchViewQ` or `bView` left.
- **Caller burden.** The backend definitions still unfolded in the bridge (`sData`, `rbPut`,
  `fkPut`, `bkOf`, `BParams.has`, `rtRange`) are older than this increment and outside its
  scope.

No finding.

### `keyView_sub` / `keyView_thin` (R12-4)

**Good.**
- `keyView_thin`'s first conjunct is now `ipureintro; exact keyView_sub hv Hsub`
  (`BackendBridge.lean:2652`).
- The statement of `keyView_thin` is unchanged.
- The rest of the proof (`snapThin`'s two halves) is its own.

No finding.

### `viewAt`, `viewAt_bView`, `viewAt_noDel` (R12-3)

**Good.**
- **`viewAt_bView`** (`InvSnapshot.lean:139-148`) is the law the header promises: from
  agreement of `γ.view`'s shares, `L` is the clients' `vd'`, and the persistent `thinV vd L`
  becomes `thinV vd vd'`. The header (`:35-39`) is now backed by a law.
- **`viewAt_noDel`** (`:152-158`) restores what `viewAtL_noDel` gave: under `dlNoDel`, the
  quarter is at `vd` itself, by `thinV_exact`. This is what D22's snapshot observer can combine
  with the server's `bucketView`, and it is in the scope the plan states ("Out": no snapshot with
  the compactor on, `backend-cmp-plan.md:30-32`; section 5).
- **The `Snapshot` spec's header** (`Spec/.../backend__Snapshot.lean:12-18`) now reads `viewAt` as
  the quarter "at a logical view the physical view `vd` is thin of". It reads `D` as thin of the
  logical view, and exact under `viewAt_noDel`. That matches the axiom: the statement is unchanged,
  and only the reading of its witness changed.

**R13-2 (second tier: "Facts that can be combined"; one definition twice).**
- **Evidence.**
  - `batchViewQ γ P st` is `∃ L, viewQ γ ¼ (vData P (st.C, st.R)) L` (`InvBackend.lean:732-733`).
  - `viewAt γ vd` is `∃ L, viewQ γ ¼ vd L` (`InvSnapshot.lean:134-135`).
  - So `batchViewQ γ P st` is, by definition, `viewAt γ (vData P (st.C, st.R))`.
  - The new `viewAt_bView` repeats `batchViewQ_bView` (`InvBackend.lean:829-838`) line for line,
    with `vData P (st.C, st.R)` generalised to `vd`.
  - The axiom's argument (round 12: "the commit's close leaves the lock's quarter at
    `viewAt γ (sData P C)`") rests on that identity, but nowhere is it stated.
- **Caller affected.** Nobody's proof today, since `viewAt_bView` has no user yet. It matters for
  the `axiom` skill's check of `backend.Snapshot`, which must see the batch lock's quarter *as* a
  `viewAt`, and for the next change to either definition, which must be made twice.
- **Restatement.** Move `viewAt` (and `viewAt_bView`) into `InvBackend.lean` beside `viewQ`.
  Define `batchViewQ γ P st := viewAt γ (vData P (st.C, st.R))`, and prove `batchViewQ_bView` as
  `viewAt_bView` at that view. `InvSnapshot` keeps its header's entry and `viewAt_noDel` (or that
  moves to `DelKeys`, which would drop `InvSnapshot`'s new `DelKeys` import). This is optional and
  costs no statement: every use of either name stays.

### `rtRes_cm_close`, `ReadSide.lean`'s header (R12-5)

**Good.**
- The docstring (`ReadSide.lean:569-575`) matches the statement (`:576-596`):
  - out of a window, `thinV (vData P (C', R.reset)) (vData P (C, R))`, and the quarter stays at
    `Lb`;
  - in a window, `thinV … L'`, with the quarter and the clients' `bView γ 1 L'` at `L'`.
- The header (`:19-25`) says the same, with the history clause.

No finding.

### The rest of the increment (brief re-check)

Statements unchanged since `f175d283b5`: `batchViewQ`, `batchGhostAt`, `viewAt`'s definition,
`commit.spec`, `unsafeCommit.spec`, `Unlock.spec`, `relog` and the `bt_*` statements.
- **`Unlock.spec`** (`Spec/.../batchTxBuffered__Unlock.lean`) has two disjuncts:
  - the deleting/no-change one: `thinV (sData P st.S) (vData P (st.C, st.R))`, the non-hook write
    buffers empty, `W ∗ Pk ∗ Q`;
  - the put one: `bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q)`.

  Against Go's `Unlock` (`batch_tx.go:328-`): the write-back under `readTx.Lock`, then `commit`
  when `pending ≥ limit` or `pendingDeleteOperations > 0`. Round 12's case analysis still applies,
  and the R12-1 repair does not touch it: it never relied on the dropped premise.
- **`unsafeCommit.spec`**: its docstring already explains `L'` out of a window (R12-6), so the
  note needs nothing more.
- **The `Snapshot` axiom**: unchanged; R13-2 concerns its vocabulary's definition, not its truth.

No first-tier finding in any of them.

## Does anything need the user?

No.
- **Exported or top-level statements:** none changed.
- **The trust base:** unchanged since round 12.
- **New families:** none; `UnsafeDelete.spec` is still one spec.
- **Still due before Freeze:** the `axiom` skill on `backend.Snapshot`, as the plan records. If
  R13-2 is taken, the skill sees the batch lock's quarter literally as `viewAt`.

## Stop rule

- This is the third round of question 2's increment.
- **The same statements draw no first-tier finding.** The one first-tier finding of round 12
  (R12-1) is repaired, and the repair introduced none.
- The repairs' leftovers are a dead `have` (R13-1) and an old stale import (R13-3).
- R13-2 is a second-tier merge of two identical definitions that R12-3's law made visible.
- **Stop reviewing this increment.** Take R13-1 and R13-3 (one line each) and, optionally, R13-2,
  without another round. Then go on to the limited-range glue and the `axiom` skill.

## Ranked by need of revision

1. **`viewAt` / `batchViewQ`**, second tier: R13-2, one definition written twice, and with it a
   duplicated law.
2. **`bt_leaseDel`** (glue), note: R13-1, the dead `have hSB`.
3. **`UnsafeDelete` spec file**, note: R13-3, the unused `DelKeys` import (pre-existing).
4. **`UnsafeDelete.spec`**, `thinV_sub`/`thinV_dl`/`relog_congr`, `keyView_sub`/`keyView_thin`,
   `viewAt_noDel`, `rtRes_cm_close` and the docstrings: no finding.
5. **`Unlock.spec`, `commit.spec`/`unsafeCommit.spec`, `relog`, `batchGhostAt`**: unchanged, no
   finding.
