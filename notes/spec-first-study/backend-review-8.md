# backend-cmp, Review round 8 (2026-10-29): the compaction keys' tracked absence, implemented

**Under review.** Commit `2e49ff1aa9` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`; `HEAD`
at review time), diffed against `2bd9536cda`. It implements the section "The compaction keys' tracked
absence (the user's choice, 2026-10-29)" of `notes/backend-cmp-plan.md`, with round 7's repairs
(`backend-review-7.md`). This round judges the Lean statements, not the plan text.

**Read.**
- Backend: `Model2.lean` (`fkKey`, `fkAbs*`, `fkInit`), `InvBackend.lean` (`fkOwn`, `fkHalf`, `fkRd`,
  `fkPut`, `rtCore`, `batchGhostAt`), `InvBatch.lean`, `InvCommit.lean`, `InvNew.lean`, `NewAlloc.lean`,
  `FkLemmas.lean`, `ReadLemmas.lean`, and the `UnsafePut`/`UnsafeSeqPut` specs.
- Trust boundary: `Spec/.../storage/OpenBackend.lean`, its axiom `Proof/.../storage/OpenBackend.lean:41`,
  `OpenSnapshotBackend` (spec and proof), `backend.Snapshot.spec`, `MustSaveMemberToBackend.spec`.
- mvcc: `InvStore.lean` (`bkNoCmp`, `metaReadSpec`, `metaReadTx`, `keyReadLocked`, `batchTxSpecG`,
  `isKeyBackendG`, the store's instances), `Image.lean`, `BackendBridge.lean`, `store__restore.lean`,
  `store__checkPrevCompactionCompleted.lean`, `UnsafeRead*Compact`, `SetScheduledCompact`,
  `rangeEvents`, `store.Restore`/`watchableStore.Restore` specs, `Results.lean`, `StoreBackend.lean`.
- Server: `InvBoot.lean` (`bootOk`), `BootBackend.lean`, `NewServer.lean:508`, `SnapApplyWalk.lean`,
  `CindexBackend.lean`, `BackendHooks__OnPreCommitUnsafe.lean`, `Results.lean`.
- Go at the pin: `server/storage/{backend,mvcc,schema}` (`mvcc/store.go:23-59`,
  `mvcc/kvstore.go:213,225-231,317-347`, `mvcc/kvstore_compaction.go:56-90`, `schema/bucket.go:26,44,82-83`).

**Build.** `lake build --no-build Proof.go_etcd_io.etcd.server.v3.etcdserver.Results
Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Results` in the worktree: all targets up to date. I did
not run `etc/tcb-report.py`: `.lake/tcb.json` is stale, as the brief says. I checked the trust base by
hand instead (see "Trust base").

**Tiers.** As in `notes/spec-first-plan.md`, "Review". Tier 1 means a requirement fails: the statement
is not true, not sufficient for a caller, or has an unneeded premise. Tier 2 is a preference.

## Summary

- **The core is right, and round 7's Tier-1 findings are fixed.**
  - The axiom is gone, and nothing replaces it: no new `axiom`, `opaque` or `sorry` in the diff.
  - The trusted `OpenBackend` now says only "what `New` gives", and `New` is proved.
  - `bootOk` no longer holds the token twice.
  - The read law goes through a persistent witness in `rtCore`.
  - `store.restore` takes its reads from the reader's clause.
- **R8-1 (Tier 1, true; Draft statement over the real backend):** the put the compaction job makes
  (the compacting range's `□ ∀ n, metaPutCap bt (U (n+1)) (U n)`) did not get the new right `MW`.
  - Over the real backend with `Cmp = True` (`isKeyBackendG_of_backendC`), the statement is now
    false: it lets a client put a compaction key without the flag's half.
  - Its `sorry` (`BackendBridge.lean:2701`) now hides an obligation that cannot be proved, where
    before it was only an unfinished one.
  - No exported result reaches it.
- **R8-2 (Tier 2):** the new default `MW := True` repeats what R7-6 removed for `NC`. For mvcc's
  assumed backend (`kb = none`), `MW = True` next to `NC = viewNoCmp` cannot be met by any honest
  creator holding `viewNoCmp`.
- **R8-3, R8-4, R8-5 (Tier 2):**
  - `fkKey` is fixed inside the backend package (coupling to the schema);
  - a few doc gaps (R7-3 item 10's trust-base lines, "given back raised");
  - `BParams.VI` could ride on the same ghost.
- **No Go bug found.**

## What is good

- **The trusted statements are true and smaller.**
  - `storage.OpenBackend.spec`'s post is `newPostK γ P W Pk K b D` alone
    (`Spec/.../storage/OpenBackend.lean:48`). The wand `⌜noCmpData D⌝ -∗ bkNoCmp γ` is gone, so the
    axiom again claims only "does what `backend.New` does".
  - `New`'s proof allocates the flag: `backend_init`, `NewAlloc.lean` (`mono_nat_own_alloc (fkInit D)`,
    then two halves). One half goes into the lock invariant (`fkHalf`), the other to the client
    (`newPostK`'s `fkOwn γ (fkInit D)`, `InvNew.lean:66,163`). The `fkRd` of the initial view is taken
    from the allocation's lower bound.
  - R7-1's arbitrary-`P` problem is gone. `fkKey` is fixed (`Model2.lean`):
    `n = "meta" ∧ k ∈ {scheduledCompactRev, finishedCompactRev}`. This matches `schema/bucket.go:26,82-83`.
  - The diff of the trusted text is visible. The meaning grew only through `newPostK`, whose
    definition `New`'s proof establishes.
  - `OpenSnapshotBackend.spec` (E) follows the same pattern, and its proof only drops `Hncmp`.
- **The duplication is gone.**
  - `fkOwn` is produced only in `backend_init`.
  - `bootOk` (`InvBoot.lean:403`) has the pure `⌜mvcc.noCmpData D⌝`. `bootBackend_of_newPost`
    (`BootBackend.lean:78-95`) turns `newPost`'s half into `bkNoCmp` (`bkNoCmp_of_fkOwn`, `Image.lean:65`).
    `NewServer.lean:508` uses it.
  - I checked every premise list that names `bkNoCmp d.γB`:
    - `etcdserver/Results.lean:825,894,1046`;
    - `mvcc/StoreBackend.lean:91`;
    - `mvcc/Results.lean:267`;
    - `BuildLemmas.lean:72`.

    None also takes `newPost`/`newPostK` or any other `fkOwn`. `SnapApplyWalk.lean:284,393` takes the
    half out of `OpenSnapshotBackend`'s `newPostK` once.
  - The caller-chosen `K`/`W`/`Pk` cannot produce `γ.fk`: the name is allocated inside `backend_init`
    before `Hmk` runs.
- **The ghost is sound.**
  - `fkHalf` lives in `batchGhostAt` and `batchGhostW` (`InvBackend.lean:295`).
  - Each transition keeps `fkAbsSt` (`FkLemmas.lean`): put of a non-`fkKey`, delete, create bucket,
    delete bucket, write-back (`wbSt`), commit (`C' = S ∨ C' = C`), `setHw`.
  - The only way to raise the flag is `fkHalf_raise`, which needs the client's half.
  - `fkRd` (`InvBackend.lean:299`) is the last conjunct of `rtCore` (`:591`). Its fact can be
    established only from `fkHalf` (`fkHalf_rd`) or from a lower bound of at least 1, which is vacuous.
  - `fkRd_abs` (`ReadLemmas.lean:974`) is the right law: `monoNatLbOwn_valid` against the half at 0
    forces the bound to be 0.
  - The client's `readTx.Lock` re-fold cannot change `rv`: the other half of `γ.rvs` stays with the
    batch lock.
- **The put specs are proved at the right level (R7-4).**
  - The inner `batchTx` puts are unchanged.
  - `batchTxBuffered.UnsafePut` takes and returns `fkPut γ bi.name kb`.
  - `UnsafeSeqPut` takes `¬ fkKey bi.name kb`. Its only caller is `bt_seqPut`, into `Key`
    (`key_not_fk`).
  - The callers' cost is one line each, `rw [fkPut_eq γ _ _ (by decide)]`, plus a `-` in the pattern:
    `CindexBackend.lean:271,337` and `BackendHooks__OnPreCommitUnsafe.lean:85`.
- **The read side (R7-2).**
  - `rt_locked` takes `fkRd γ P rv` (`BackendBridge.lean:1342`).
  - `bridge_rt`, `bridge_rt_clean` and `bridge_rtC` get it from `rtHeld_fkRd`.
  - `rt_metaNone` (`:686`) proves `metaReadSpec … true` under the reader's own `rtTok` through
    `rtRange_fkAbs`, which covers both the committed bucket and the read buffer.
  - The clause `□ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok)` sits in `keyReadLocked`'s `rng` branch
    (`InvStore.lean:676`, `keyReadLocked_meta` `:719`), anchored to the reader's `Tok`.
  - `store.restore` uses it at `store__restore.lean:89,601`, consuming `kbNoCmp` as its spec says.
  - This matches Go: `restore` does `ReadTx(); RLock()` and then both reads (`kvstore.go:327-342`).
- **`NC` is explicit everywhere (R7-6).** It appears with no default on `keyReadLocked`,
  `keyReadSnap(C)`, `isKeyBackendG` and `keyCleanRead`. `store.restore.spec` names
  `kbNoCmp γ.kb γ.bucket` in its `isKeyBackendG` (R7-3). `store.Restore` and `watchableStore.Restore`
  name it in `keyCleanRead`, and `rangeEvents` quantifies it.
- **`metaReadSpec`/`metaReadTx` with `Tok` and `Rd` (question 3).**
  - The spec is persistent (`metaReadSpec_persistent`).
  - The `UnsafeRead*Compact` specs take `□ metaReadSpec rt nc Rd Tok ∗ rdCap Rd Tok ∗ Tok` and return
    `Tok`. Their proofs read the value through `rdCap` and give the fraction back.
  - `checkPrevCompactionCompleted` threads `Tok` from `RLock` to `RUnlock`, as Go's `defer tx.RUnlock()`
    does (`kvstore.go:225-231`).

## Findings

### R8-1 (Tier 1, true; a Draft statement over the real backend). The compaction job's `Meta` put has no `MW`

- **Evidence.**
  - `batchTxSpecG`'s limited-range clause (`⌜Cmp⌝ -∗ …`, `InvStore.lean:1165-1195`) gives
    `(□ ∀ n : Nat, metaPutCap bt (U (n + 1)) (U n))` (`:1193`).
    - This is the put of `finishedCompactRev` that the compaction job makes in the same session as its
      last range and deletes: `kvstore_compaction.go:56-71`, `UnsafeSetFinishedCompact(tx, …)` then
      `tx.Unlock()`.
    - The commit gave `MW` only to the other `Meta` clause, the fresh session's put
      (`SetScheduledCompact`'s, `:1200`).
  - Over the real backend this put is `batchTxBuffered.UnsafePut` at an `fkKey`, which now needs
    `fkPut γ "meta" k = ∃ f, fkOwn γ f`. The bridge chooses `U`, but it does not have the client's half
    when the range runs, so it cannot put the half inside `U`.
  - So `isKeyBackendG_of_backendC` (`BackendBridge.lean:2630`, `Cmp = True`,
    `NC = bkNoCmp γ`, `MW = ∃ f, fkOwn γ f`) is now false as stated, in this clause:
    1. A client holding `bkNoCmp γ` runs the limited range.
    2. It puts `finishedCompactRev` through the `U`-clause without spending its half, then unlocks.
    3. `ReadTx`/`RLock`, then the reader's clause with `NC` (still held), claims that the key is absent.
       Go returns it.
  - The case is the `sorry` at `BackendBridge.lean:2701`. The commit's note ("its `sorry` is
    unchanged") is true of the text, but the obligation behind it went from unfinished to impossible.
- **Who is affected.**
  - `isKeyBackendG_of_backendC` and the wiring step that will switch the real store to it
    (`InvStore.lean:1644`, `InvCompact.lean:184`).
  - No linked or exported result reaches it today: it has no user outside `BackendBridge.lean`. That is
    why this is Tier 1 for the Draft and not a soundness hole in the results.
- **Restatement.** Give the step put the same right, given back:
  `(□ ∀ n : Nat, metaPutCap bt iprop(U (n + 1) ∗ MW) iprop(U n ∗ MW))`.
  - For mvcc's assumed backend (`MW = True`) nothing changes: `UnsafeSetFinishedCompact`'s caller frames
    `True`.
  - For the real bridge the case becomes provable from `bt_metaPut`'s pattern (`fkPut` from `MW`).
  - The compaction job must then hold `MW`, the store's half. That is the same decision as
    `SetScheduledCompact`'s and the plan's "left for the wiring step": the store keeps the half instead
    of `restore` consuming it.
  - The plan's sentence "No proved store uses that clause over the real backend" should name both
    `Meta` clauses.

### R8-2 (Tier 2, shape; R7-6 again). The default `MW := True`, and its `kb = none` instance

- **Not a second family, and not unsound by itself.**
  - It is one definition. Every real-backend statement that keeps the default has `Cmp` false:
    - `isKeyBackendG_of_backend` (`hC : ¬ Cmp`, `BackendBridge.lean:2390`);
    - `storeBackend`/`storeBackendT`/`physOk` over `kb = some d`, where `storeCmp = (kb = none)`
      (`InvStore.lean:1645`).
  - So the clause is vacuous there, and `MW` does not matter.
  - A wiring that forgot `MW` would also fail to type-check against `isKeyBackendG_of_backendC`: you
    cannot derive `metaPutCap (Locked ∗ True)` from `metaPutCap (Locked ∗ ∃ f, fkOwn γ f)`. The default
    is not a silent hole.
- **Why drop it anyway.**
  - It is invisible at the use site. R7-6 dropped `NC`'s default for exactly this reason, and the plan
    defends `MW`'s default by `SR`/`SRh`'s precedent, which R7-6 already weighed.
  - Name it in `storeBackend`, `physOk` and `storeBackendT` as `kbMW γ.kb …`, the way `kbNoCmp`,
    `kbRb` and `kbBt` are named.
- **The `kb = none` instance is not satisfiable by an honest creator holding `viewNoCmp`.**
  - Its contract has `Cmp = True` and `MW = True` (puts of compaction keys at no cost) next to
    `NC = viewNoCmp γb` (the reader's clause: "none found").
  - A holder of `viewNoCmp` can put a key, commit, read it, and be told by the clause that it is absent.
  - Before this commit the refuted axiom covered `kb = none` too. Now the problem is only a premise (no
    `axiom`), and `viewNoCmp` has no supplier in the repository (`InvStore.lean:475`, no other use).
    So results over `kb = none` that take `kbNoCmp` are vacuous rather than wrong.
  - **Restatement (when it matters):** mirror the real backend. Use an opaque `viewFk γb n` with
    `viewNoCmp γb := viewFk γb 0`, and `MW := ∃ f, viewFk γb f` for `kb = none`.
- *Uncertain:* who would prove `storeBackend` for `kb = none` (R7-3 item 6). I found no one, as in
  round 7.

### R8-3 (Tier 2, coupling / implementation independence). `fkKey` is mvcc's schema baked into the backend

- `fkKey` (`Model2.lean`) names `"meta"`, `"scheduledCompactRev"` and `"finishedCompactRev"` inside the
  backend package. Go's backend is schema-agnostic.
- The plan justifies it ("the backend serves one schema"), and it removes R7-1's arbitrary-`P` half
  cheaply. But the hook keys (`P.hk`) and tracked buckets (`P.RB`) are parameters of `BParams`, while
  these keys are not.
- If a second tracked-absent key is ever needed (another component's "not yet written" fact), it
  becomes a backend change.
- The alternative remains R7-1's: `P.FK` with `bridgeParams`' conjunct `P.FK = cmpFK` and `Wf`'s
  "`FK` key not an `hk` key".
- I accept the choice. It should be recorded as a decision in `notes/decisions.md` (it is only in the
  plan's Done list, "Decided by the agent").

### R8-4 (Tier 2, know the margin; docs)

- **"Given back raised".**
  - The `UnsafePut` docstring says the half is "given back raised"
    (`Spec/.../batchTxBuffered__UnsafePut.lean:33-34`). `fkPut`'s docstring says the same
    (`InvBackend.lean:305-307`).
  - But the post is `fkPut γ bi.name kb`, that is `∃ f, fkOwn γ f`. The bound `f ≥ 1` is not in the
    post.
  - No caller needs it: `bt_metaPut` re-quantifies. Say "given back (at some value; the code's: at least
    1)", or drop "raised".
- **R7-3 item 10 is not done.**
  - Several axioms' meaning moved through `batchLocked`/`isBackend`, which now carry `fkHalf`:
    - `backend.backend.Snapshot` (it only commits: `Spec/.../backend__Snapshot.lean`);
    - `schema.membershipBackend.MustSaveMemberToBackend` (puts to `members` only);
    - `MustUnsafePutLease`/`UnsafeDeleteLease` (the caller's triple).
  - They are still true, but the plan's Done section and the axioms' docstrings do not say so. Add one
    line each to the trust-base note.
- **`rtCore`'s docstring** names the update points of `fkRd` as the constructor, the write-back and the
  commit. R7-5 also named `CommitAndStop`. The build shows that every re-fold of `rtCore` supplies
  `fkRd`, but the docstring should say whether `CommitAndStop` goes through the commit path.
  *Uncertain:* I did not trace it.

### R8-5 (Tier 2, scope; question 4). `BParams.VI` could ride on the same ghost

- `metaReadTx`'s value case over the real backend is still the `sorry` at `BackendBridge.lean:2749`. It
  needs a value invariant: values at compaction keys are `metaRevVal`.
- `fkHalf` is already the one place every write of these keys passes through.
- A conjunct "every `fkKey` value in `st` satisfies `metaRevVal`" would:
  - be kept by `fkHalf_put`, since `metaPutCap` already requires `metaRevVal v` and `UnsafePut` would
    take it when `fkKey`;
  - be read by `rtRange` like `fkAbsRv`.
- That would close question 4 without a new `BParams` field. Its cost is a premise on the opened file
  `D` (its values at these keys are well formed) in `fkInit`/`newPostK`, a fact about the file like
  `noCmpData`.
- This is a suggestion for the next step, not a defect.

## R7 findings: status at `HEAD` (`2e49ff1aa9`)

- **R7-1: fixed.** The wand is dropped from `OpenBackend` and `OpenSnapshotBackend`. `bootOk` holds a
  pure `noCmpData D`. `bkNoCmp := fkOwn γB 0`, with `bkNoCmp_of_fkOwn`. The keys are fixed (`fkKey`)
  instead of `P.FK`; see R8-3. There is no second `fkOwn` beside any `bkNoCmp` premise.
- **R7-2: fixed.** `fkRd` is in `rtCore`, with `rtHeld(F)_fkRd`, `fkRd_abs` and `rt_metaNone`.
- **R7-3: fixed**, with three exceptions:
  - the `kb = none` supplier is still open (R8-2);
  - item 10's trust-base lines are missing (R8-4);
  - item 5 (`bridgeParams` gains `P.FK = cmpFK`) is moot under `fkKey`.
- **R7-4: fixed.** The inner specs are unchanged; `fkPut` is on `batchTxBuffered.UnsafePut`, and
  `¬ fkKey` is on `UnsafeSeqPut`.
- **R7-5: moot / fixed.** There are no `Wf` clauses. The update points are named by `rv` in `rtCore`'s
  docstring (`CommitAndStop`: R8-4).
- **R7-6: fixed for `NC`**, but repeated for `MW` (R8-2).

## Trust base

- The axiom `mvcc.kbNoCmp_metaNone` is deleted, together with `NoCmpRead.lean`. No import of
  `NoCmpRead` remains. The remaining mentions are in comments (`InvStore.lean`, `BackendBridge.lean`,
  `store__restore.lean`).
- It is removed from `etc/tcb-baseline.txt:570` and from the ten collections.
- No line added in the diff contains `axiom`, `opaque`, `sorry`, `admit`, `native_decide` or
  `implemented_by` outside comments.
- `sorry`s in the changed files are all pre-existing (the same lines at `2bd9536cda`):
  - `BackendBridge.lean:2701`: the compacting range. Its obligation is now unprovable (R8-1).
  - `BackendBridge.lean:2749`: `metaReadTx`, `BParams.VI`.
  - `NewServer.lean:1980`: M2 S4.
  - `newBackend.lean`/`BboltOptions.lean`: these mention the generated `sorry -- axiomatized type` only
    in comments.
- `backend.New`'s proof, which now carries the trusted `OpenBackend`'s meaning, has no `sorry`.

## Go code

- No bug found.
- Every write of a compaction key goes through `BatchTx().UnsafePut`:
  - `mvcc/store.go:47,59`, from `kvstore.go:213` (`SetScheduledCompact`);
  - `kvstore_compaction.go:70` (`UnsafeSetFinishedCompact`, in the job's session).
- No `issues/` entry is needed.

## Ranked by need of revision

1. **R8-1** (Tier 1): the compaction job's `Meta` put in `batchTxSpecG`'s limited-range clause needs
   `MW`. `isKeyBackendG_of_backendC` is false as stated, and its `sorry` at `:2701` cannot be proved.
2. **R8-2** (Tier 2): drop `MW`'s default and name `kbMW γ.kb`. Make the `kb = none` instance
   satisfiable (an opaque `viewFk` mirroring `fkOwn`).
3. **R8-4** (Tier 2): the docs. "Raised" is not in the post; add the trust-base lines for `Snapshot`,
   `MustSaveMemberToBackend` and the lease axioms; settle `CommitAndStop` in `rtCore`'s docstring.
4. **R8-3** (Tier 2): record the fixed `fkKey` as a decision.
5. **R8-5** (Tier 2, suggestion): carry `BParams.VI` on the flag's ghost.

Targets ranked by need of revision:
1. `batchTxSpecG`/`isKeyBackendG` (mvcc's contract): R8-1, R8-2.
2. `isKeyBackendG_of_backendC` (the bridge): it follows R8-1.
3. `batchTxBuffered.UnsafePut.spec`: R8-4's wording only.
4. `fkKey`/`fkOwn`/`fkRd`/`fkPut` and the read laws: R8-3 only.
5. `storage.OpenBackend.spec`, `OpenSnapshotBackend.spec`, `newPost(K)`, `bootOk`,
   `bootBackend_of_newPost`, `bkNoCmp`, `store.restore`/`store.Restore`/`watchableStore.Restore`,
   `rangeEvents`, `UnsafeRead*Compact`, `UnsafeSeqPut`: no change needed.
