# Axiom review: `backend.backend.Snapshot.wp_proof`, the compaction-key flag draft (2026-11-02)

**Outcome.** The proposed restatement below (the post's `fkRd γ P (D, ⟨∅, W64 0⟩)`, `Q`
unchanged) is the one taken, with the user's approval (2026-11-02), in place of the reviewed draft.

**Reviewed.** The draft change only, against the files on branch `snap-window`
(`/shared/etcd-grove-window`, `cf425c5140`):

- the new `fkLbAbs γ φ := ∃ f, monoNatLbOwn γ.fk f ∗ ⌜f = 0 → φ⌝` (`InvSnapshot.lean`);
- `Q` gains a fourth argument (a `Prop`); the observation also receives `fkLbAbs γ fa` for every
  `fa`, and the post gives `Q … (fkAbsD D)`.

The rest of the axiom (the commit, `viewAt`, `hkOwn`, `rbOwn`) is out of scope. Go code:
`server/storage/backend/backend.go:381-423` at the etcd pin.

**Verdict: survives.** I found no gap, so there is no counterexample program and nothing was built.
The draft is sound and its docstring's justification is right. A simpler statement that also says
more is proposed below.

## Why it is sound

Soundness reduces to one claim. At the moment the observation is used (the end of the last bbolt
commit before `Begin(false)`), `fkLbAbs γ (fkAbsD D)` holds in the real ghost state, alongside the
resources the axiom already claims. It does:

- The flag's authority is split into the lock's half (`fkHalf`) and the client's half (`fkOwn`),
  and the two agree on its value. Whoever holds the lock's half can take `monoNatLbOwn γ.fk f` at
  its current value `f` (`monoNatLbOwn_get`, as `fkHalf_rd` does).
- After a commit, the lock's half is `fkHalf γ P (commitSt st' C' …)`, by `fkOkG_commit`
  (`FkLemmas.lean:552`, used in `InvCommit.lean:66`). So `fkOkG P f g st` holds with `st.C = C' = D`,
  and `f = 0 → fkAbsSt P st → fkAbsRv P (st.C, st.R) → fkAbsD D`.
- `st.C` changes only at a commit, so the same holds at every moment until the next commit, which
  by assumption comes after `Begin`. This also covers the case where the call's own `Commit` finds
  nothing pending.
- This is the step `batchTxBuffered.unsafeCommit` already proves for the concurrent readers
  (`batchTxBuffered__unsafeCommit.lean:182`: `fkHalf_rd` at the commit's end gives every reader
  `fkRd γ P (C', R.reset)`). The axiom claims for the snapshot's read transaction what the proved
  code establishes for the backend's own read transactions.

## Attacks tried

1. **A lower bound below what is true of `D`.** Ruled out. The flag never decreases, and a lower
   bound at `f` only claims `f = 0 → fkAbsD D`.
   - A put of a compaction key raises the flag first (`fkPut` needs the client's half), so a key
     cannot appear in `D` while a lower bound of `0` is still truthfully obtainable.
   - Suppose a later commit (the `run` goroutine's, or an `Unlock`'s) lands between `Snapshot`'s
     `Commit` and its `Begin`, after a put of a compaction key. Then the lower bound is taken at
     that later commit, at `f ≥ 1`, and says nothing.
   - Deletes cannot break absence (deletion only adds absence). The model does not allow
     `UnsafeDelete`/`UnsafeDeleteBucket` on the `meta` keys anyway (`fkOkG`'s docstring).
2. **Choosing `fa` adversarially.** Ruled out. The caller never picks `fa`: the post fixes it at
   `fkAbsD D`. The quantification over `fa` is an obligation on the caller; it constrains only the
   caller.
   - `fkLbAbs γ False` is equivalent to `∃ f ≥ 1, monoNatLbOwn γ.fk f`. That needs the flag to be
     at least `1`, so it cannot be had while the flag is `0`. At `0` it contradicts `fkOwn γ 0`
     (`monoNatLbOwn_valid`).
   - `fkLbAbs γ True` always holds (a lower bound of `0`). So a `Q` such as `fun … fa => ¬fa` has an
     observation that cannot be proved, which is as it should be.
   - Lean's `Prop` is extensional (`propext`), so `Q` cannot tell `fkAbsD D` apart from an
     equivalent proposition.
   - A premise that is "too strong" would be one the axiom cannot supply at the real moment. It
     supplies it only at `fa := fkAbsD D`, which is justified above.
3. **The caller's `R` against the lock's half.** No contradiction. If `R` holds `fkOwn γ n`, the
   flag stays at `n` through the call (changing it needs both halves), so any lower bound is
   `f ≤ n` and consistent with `R`. A committer that holds the client's half while it commits
   rules out `R` holding it (the half is exclusive).
4. **The compaction's writes racing with `Snapshot`.** Each one is an `UnsafePut` under the batch
   lock. `store.Compact`'s `UnsafeSetScheduledCompact` and the job's `UnsafeSetFinishedCompact` go
   through `fkPut`, which raises the flag. They reach `D` only through a commit, which is attack 1.
5. **Other writers of the compaction keys.** None reach `D` without raising the flag.
   - The hooks (cindex: `consistent_index`, `term`) do not write them. `commit_ghost` takes the
     post-hook state's `fkHalf`, which is proved, not assumed.
   - Defragmentation (under `b.mu.Lock`, excluded while `Snapshot` holds `RLock`) copies the data
     unchanged.
   - A restore opens a new backend with new names.
6. **Go-level panic.** Nothing to attack. The draft adds only ghost facts: `Snapshot`'s body is
   unchanged, and its one failure path (`lg.Fatal` on `Begin`) is the existing axiom's claim.

**Not tried:** a Lean proof. I did not build the draft's statement or a client that uses it.

## Proposed restatement (simpler, and says more)

Leave `Q` with three arguments and put the reader's flag fact in the post:

```
post: snapOpen sp D ∗ bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, W64 0⟩) ∗
      ⌜Q (sData P D) (hkData P D) (rbData P D)⌝
```

(`⟨∅, W64 0⟩` is the empty read buffer, as in `sData`.)

- **Justified by the same argument.** `fkHalf_rd` at the end of the last commit, with
  `fkOkRvG_of ∘ fkOkG_commit`, gives `fkRd γ P (D, R.reset)`. The read buffer's half of `fkOkRvG`
  (`fkAbsB`, `fkWfB`) is trivial on empty buckets, so `fkRd γ P (D, ⟨∅, W64 0⟩)` follows. This is
  exactly the fact the proved commit gives every reader.
- **Says more than the draft.** `fkRd` implies `fkLbAbs γ (fkAbsD D)`. It also gives the open's
  values (`fkRd_open`) and well-formedness (`fkRd_wf`) for free, and the client reuses the existing
  laws: `fkOwn γ 0 ∗ fkRd …` gives `fkAbsD D` by `fkRd_abs`.
- **Smaller change.** `Q` keeps its arity, so no existing caller's observation changes. `fkRd` is
  persistent and `R` (holding `fkOwn γ 0`) is returned, so a post-state fact serves the intended
  use as well as the observation's argument does.
- **What it gives up.** The only thing lost is combining `fa` with `W`/`Pk`/`viewAt` inside the
  observation, which the intended use does not need.

If the draft's form is kept, its docstring should name the two lemmas the argument rests on
(`fkOkG_commit`, so `fkAbsD` of the committed data; `monoNatLbOwn_get` on the lock's half) and the
proved counterpart (`unsafeCommit`'s `fkRd` of the readers).
