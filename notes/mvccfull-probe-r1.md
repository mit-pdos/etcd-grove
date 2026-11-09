# mvccfull Probe: B3's R1 and R2 (2026-11-09)

The question: does `rtHeldDlsLaw` (`Proof/.../mvcc/NewCleanRead.lean`) hold, and can the backend's
invariant prove it? It says that a held reader misses, of the clients' clean view, in a safe-range
non-hook bucket, only entries in the client's half of the deleted entries `dlsOwn γ X`.
R2 asks whether the view stays clean through `NewStore`'s batch session.

## Verdict on `rtHeldDlsLaw`

**It is true of the Go code, and the current definitions cannot prove it.**

- **Why it cannot be proved now.** The law is an entailment from `rtHeld ∗ bViewC ∗ dlsOwn`.
  - `rtHeld` relates the reader's missing entries only to the registration. Through `rtResAt` →
    `rtRest` → `viewQ`, each one is `thinV`'s `dlIs` (`InvBackend.lean` l.876-890).
  - The ghost `γ.dls` has exactly two halves:
    - the client's, `dlsOwn`;
    - the batch lock's, `fkHalf` (l.652), inside `batchFree`/`batchLocked`.
  - The batch lock's state cannot be reached by an entailment. Neither can its pure `dlsW`/`dlsOk`
    (l.373-391), the only place where "logical entries missing from the contents are in `dl`" is
    recorded.
  - So a resource exists that satisfies `rtHeld ∗ bViewC γ q vd true ∗ dlsOwn γ ∅` and whose
    `vData P rv` lacks an entry of `vd`. Its only witness is `dlIs`, from any registration.
  - Specialising to `X = ∅` does not help. With `storeDlReg` fixed, `dlIs` yields only `▷ (keyName ∗
    delKeyI …)`. A restored store's compaction can make that true: the records of a resumed
    compaction are deletable.
- **Why it is true of the Go code.**
  - `BSess.dl` only grows. `BSess.del` (`Model2.lean` l.340) is its only writer; nothing resets it.
  - Both halves of `γ.dls` change together only in the delete (`InvBatch.lean` l.381).
  - A reader's state `rv` and the logical view `L` change only under the batch lock:
    - the `Unlock` write-back (`batch_tx.go` `Unlock` → `writeback`);
    - the commit (`unsafeCommit`, under `readTx.Lock()`).
  - At those points, a safe-range entry of `L` that the new physical view lacks was deleted since
    the open (`dlsOk.1` with `viewSame_of_freeOk`). Puts and deletes change neither `L` nor `rv`,
    and deletes only grow `dl`.

## The strengthening (option 2; prototype in `Proof/.../backend/RtHeldDls.lean`, builds, no `sorry`)

1. **`dlsOwn γ X := ghostMapAuth γ.dls ½ X`**, in place of a `ghostVar`. It keeps the same name,
   so `BNames` is unchanged. Each delete mints a persistent witness `dlSeen γ nk := ∃ v,
   nk ↪[γ.dls]□ v`.
   - The insert is always fresh. `dlsS` (always in `dlsW`) says a deleted safe-range entry is
     missing from the writer's contents, and `BSess.del` inserts only a present key, so it never
     overwrites.
   - Proved: `dlsOwnM_insert` and the lookup `dlCov_dlsOwnM`.
   - Also needed: the batch lock keeps the witnesses of `dlR P st.dl`. Add a conjunct
     `□[∗map] nk↦v ∈ dlR P st.dl, nk ↪[γ.dls]□ v` to `fkHalf`, or fold it into `dlsOwn`.
2. **`rtCore` gets a conjunct `dlCov γ P (vData P rv) L`**: every safe-range non-hook entry of `L`
   missing from `vData P rv` is `dlSeen`. Make it a separate conjunct, so `thinV` is unchanged.
3. **`batchViewQ` gets a pure conjunct**: every safe-range non-hook entry of `L` missing from
   `vData P (st.C, st.R)` is in `st.dl`. The re-established `dlCov` needs it.
   - `Lock`, put, delete and `CreateBucket` preserve it trivially: `C`, `R` and `L` are unchanged
     and `dl` only grows.
   - At the write-back and commit, `dlsOk.1` re-establishes it, as it does `dlsW` today.
4. The law then follows from a projection lemma `rtHeld_dlCov` (shaped like `rtHeld_clean`):
   `rtHeldDlsLawM_of`, proved. With it, `keyCleanRead_of_backendD` holds as already written.

**What re-breaks:**

- Every proof that destructures `rtCore` with an explicit pattern (the `…, #Hfk⟩` patterns):
  `ReadSide` (14 mentions), `ReadLemmas` (7), `NewLemmas`, `NewAlloc`, `ConcurrentReadTx`,
  `readTx.UnsafeRange`.
- The places that set `rv`: `wb_core`, `rtRes_cm_close`, the stop's commit, the constructor (exact
  there, trivial).
- Every user of `dlsOwn` (17 files) whose proof calls `ghostVar_agree`/`ghostVar_update` on it:
  `InvBatch` l.381, `SnapFreeze` l.457, `NewAlloc`'s allocation.
- Estimate: 200-400 changed lines, all in the backend except two mvcc call sites. The rebuild
  covers all of backend and mvcc, and `dlsOwn` is client-visible ghost state. So this goes to the
  user.

## Recommended instead: no backend change (option 3's "weaker statement")

`NewR.lean` step 4 says that "`RC := dlInit` with step 2 postponed is impossible: the batch session
needs the contract". This is not so:

- **The session needs no registration.** `NewStore`'s session uses only `BatchTx`, `ForceCommit`
  and `batchTxInitSpec`: `LockOutsideApply`, `UnsafeCreateBucket`, `Unlock`
  (`NewStore.lean` l.408-490).
- **A contract without the registration exists.** `isKeyBackendG_of_backendC`
  (`BackendBridge.lean` l.3320) builds the contract at `delKey := bkDel γB`, from `isBackend`,
  `keySized` and `fkV` only.
- **The Go order allows a late fix.** `restore()` (`kvstore.go` l.327-407) reads under `tx.RLock`
  and does nothing that deletes before `RUnlock`. The resumed `compactLockfree` (l.412) runs
  after it, through `restore.spec`'s continuation `resumeK … restoreDone` (the read token `RT`
  given back).
- **The restatement.** `NewStoreR` takes:
  - the session contract at `bkDel`;
  - `restoreRegM d` (that is, `dlInit`);
  - `restoreFixM d γ -∗ storeBackendTR …`;
  - the clean read `keyCleanRead_of_backendC`, lent `storeRT γ ∗ dlInit`. It exists and is proved.

  This is exactly `store.Restore`'s pattern. The proof fixes the registration in the resume
  continuation (`restoreRegM_fix`), and `isKeyBackendG_congrDel`/`storeDlReg_congr` relate the two
  contracts. `NewR`'s glue postpones step 2 until after the call, and `cleanRead_of_image` is not
  needed.

## R2: the view stays clean through the session

**The existing contract gives it, with nothing new.**

- The client's `bViewC γ q vd true` is pure ghost ownership. The session takes none of it:
  - `UnsafeCreateBucket` (no view in its pre);
  - `Unlock`'s deleting branch (`thinV` of the session, `W ∗ Pk ∗ Q`; no clients' share);
  - `ForceCommit`.

  The client frames it.
- The deleting branch's premise holds: `viewSame` of a create-only session (`viewSame_create`,
  `BackendBridge` l.1737), then `viewSame_thin`.
- The write buffer is empty off the hook's buckets: `UnsafeCreateBucket` does not touch `W`.

## Notes

- **A tactic snag.** In a context generic in `hlc`, `imod` of `ghost_map_insert_persist` into a
  `|==>` goal fails ("not a modality"); into `|={E}=>` it works. This is a possible Perennial or
  Iris ElimModal gap and was not investigated.
- **No Go bug found.**

## Done: R1 settled by restating B3 (2026-11-09, the coordinator's decision)

The no-backend-change route was taken. The `rtHeldDlsLaw` strengthening stays a recorded alternative
only (`backend/RtHeldDls.lean`). `NewCleanRead.lean` was deleted: nothing imported it. Its bridge
lemma's target `mvcc.NewStore.cleanRead_of_image` (in `NewR.lean`) was removed too.

**The open point, settled.**
- `batchTxInitSpec` (`InvStore.lean` l.1758) takes only `RT WT W Wi Dep LockedO P`.
- The contract's `ForceCommit` clause takes `RT WT Req`.
- These two are all that `NewStore`'s session uses (`NewStore.lean` l.408-490). Neither names `NC`
  (`kbRecs` vs `bkNoCmpF`) or `Del`.
- So a session contract at any `Del`, at `NC = kbNoCmpF`, suffices. This is `mvcc.storeSessT`
  (`mvcc/NewStoreSess.lean`).

**Statements changed.** The changes are the same in `NewStore.specR` (`NewStoreR.lean`),
`newWatchableStore.specR` and `New.specR`:
- the contract `∃ Dep, isKeyBackendGR … (delKey γ) …` became three things:
  - `storeSessT b s γ P`;
  - `restoreFixM d γ -∗ storeBackendTR b s γ P r`;
  - `restoreRegM d`;
- the clean read is now lent `storeRT γ ∗ restoreRegM d` (it was `storeRT γ ∗ RC`);
- `RC` left the parameters, the pre and the post.

The fresh instances (`spec_of_specR`, `sorry`) now take `storeBackendT` and the clean read lent
`restoreRegM d`. `NewR.lean`'s outline steps 2 and 4 are corrected. `ApiNewRestoring.lean` is
unchanged.

**Proved** (no `sorry`):
- in `NewStoreSess.lean`:
  - `storeSessT_session`: what the session uses;
  - `storeSessT_of_storeBackendT`;
  - `storeSess_fix`: `restoreRegM d ∗ (restoreFixM -∗ storeBackendTR) ⊢ |==> storeBackendTR`;
  - `storeSess_restoreView`;
- in `NewStoreSessReal.lean`: `storeSessT_of_backendC`, the real backend's session contract at
  `bkDel` with no registration;
- in `NewStoreLineup.lean`:
  - `sess_W_of_Wi`: the session's `Unlock` takes back `LockOutsideApply`'s `Wi`, because `kbWi =
    storeW = lateW` at a real backend;
  - `restore_inputs`: the image gives `restoreViewR … 1 false` with `NC`, the values and the cut;
  - `restoreDone_fix`: the fix from `restore()`'s returned token.

**A finding for `NewStore`'s B3 proof.** The fresh proof registers the store at the session's
`Unlock` (`storeW_register` with `writerRes` at `[[], []]`). Over the image this is impossible: the
writer's `bucketViewL` at `[[], []]` would need the bucket empty. B3 must give the `Unlock` the
unregistered `Wi`, keep the registration pending (`writerReg`'s `kbRegRight ∗ writerRes`
disjunct), and build `writerRes` at `L'` after `restore()`, as `store.Restore` does. The view goes
whole to `restore()`.

**A tactic issue.** `imod` of a `|==>` hypothesis into a `|==>` goal fails with "not a modality" in
these modules. `|={E}=>` goals work.
