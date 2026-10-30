# backend-cmp, Review round 7 (2026-10-29): the compaction keys' tracked absence

**Under review.** The last section of `notes/backend-cmp-plan.md` ("The compaction keys' tracked
absence (the user's choice, 2026-10-29)", lines 796-842). Commit `2bd9536cda` (branch `backend-cmp`,
worktree `/shared/etcd-grove-be`). Since round 6 there are two commits, `db40a519ec` and
`2bd9536cda`. Both change only the notes. No Lean was written, so this round reviews a design, not
statements.

**Read.**
- The backend: `Model2.lean`, `InvBackend.lean`, `InvBatch.lean:40`, `InvNew.lean:58,156`, and the
  put, read and lock specs under `Spec/.../storage/backend/`.
- The trust boundary and its callers: `OpenBackend.lean`, `InvOpen.lean`, `OpenSnapshotBackend.lean`.
- mvcc: `InvStore.lean`, `NoCmpRead.lean`, `BackendBridge.lean` (`rt_locked`, `bridge_rt*`),
  `store__restore.lean`, and the specs of `store.restore`, `store.Restore`,
  `watchableStore.Restore`, `UnsafeReadFinishedCompact` and `NewStore`.
- The server: `InvBoot.lean`, `BootBackend.lean`, `Results.lean`.
- The axiom review: `axiom/kbnocmp-metanone:notes/axiom-review/nocmpread.md`.
- Go at the pin: `/shared/etcd-grove/.lake/go-src/etcd/server/storage/{backend,mvcc,schema}`.

**Tiers.** As defined in `notes/spec-first-plan.md`, "Review". Tier 1 means a requirement fails:
the statement is false, insufficient for a caller, or has an unneeded premise. Tier 2 is a
preference.

## Summary

- **The core mechanism is sound.** Every Go path that writes a compaction key goes through
  `UnsafePut`. Defragmentation and the other paths add no key.
- **The plan's wording has three Tier-1 defects.**
  - **R7-1:** `OpenBackend`'s "same text, new meaning" is false as stated. There are two
    independent reasons, and the same duplication also makes `bootstrapContract` unsatisfiable.
  - **R7-2:** the read law the plan names cannot prove the mvcc clause.
  - **R7-3:** "`store.restore`'s spec unchanged" is not true. The list of statement changes misses
    about ten statements, several of them trusted or exported.
- **R7-4 (Tier 1, local to the package):** the plan puts `fkPut` on the inner `batchTx` puts. Those
  specs cannot be proved.
- **The ghost (question 2) is the right one.**
- **The clause (question 3) is sound and usable.** But the restore spec must name `NC`. The default
  `False` is not a second family. Still, it is better dropped (R7-6).
- **No Go bug found.** I checked the fork's non-blocking defrag as a candidate. It does not
  resurrect or add keys.

## What is good

- **It fixes both faults of the refuted axiom.**
  - *Anchoring.* The clause lives inside `keyReadLocked` for the reader's own `rt`. Its `Tok` is the
    bridge's `rtTok γ P b rtx rv rdOpen` (`BackendBridge.lean:553`), which pins `rtx` and `rv`.
    `L := False` no longer helps: with `L := False` one never reaches `keyReadSnap`'s post, so one
    never gets a `keyReadLocked`.
  - *Persistence.* The persistent `□ metaReadSpec rt true Rd Tok` is true for as long as `Tok`
    exists:
    - `readTx.UnsafeRange` returns `rtRange rv …` (`readTx__UnsafeRange.lean`).
    - `rv` cannot change while `Tok` is held. Both the write-back and the commit take
      `readTx.mu.Lock` (`batch_tx.go:330`, `:376`).
    - A later `RLock` that sees a compaction key has a different `rv`, so a different `Tok`.
    - Monotonicity does the rest. If `NC` (the flag at 0) is shown at any time, then the flag was
      0 when `rv` was set.
- **Every Go writer of the keys goes through `UnsafePut`.** `grep` over the server finds exactly
  two writes, `mvcc/store.go:47` and `:59`. The other `Meta` writes are of other keys:
  `schema/cindex.go:89,93`, `confstate.go:35`, `version.go:61`.
- **Every other path adds no compaction key.**
  - Deletes, bucket creation and bucket deletion only remove keys.
  - The pre-commit hook returns `batchLocked γ P b st'` (`InvBackend.lean`, `hooksSpec`), which
    carries `batchGhostAt` and therefore the new clause. Its own puts are `hk` keys, which are not
    `FK` (the new `Wf`).
  - Defragmentation is unspecified. In Go it only copies:
    - the blocking defrag copies everything;
    - the non-blocking defrag copies only the safe-range buckets in phase 1
      (`backend.go:892-898`), and re-copies the others whole in phase 2 (`:1019-1029`);
    - safe-range deletes are excluded throughout (`:699`).
  - `backend.Snapshot` (an axiom) only commits. A received image is a new backend whose flag is
    set from its own file.
  - `readTx.Lock` gives the client all of `rtRes` (`readTx__Lock.lean`). The client still cannot
    move `rv`: the other half of `γ.rvs` stays with the batch lock.
- **The new meaning of `OpenBackend` needs no new environment assumption.**
  - The flag claims something about the backend's whole life: no compaction key appears except
    through the holder's put.
  - That rests on bbolt being exclusive, which `newPostK` already assumes through `ownDB`/`isBackend`
    and `dbOpensOk` (`InvOpen.lean:10-16`: no other process holds the file's lock).
  - The axiom already claims the backend model for the backend's life. The flag adds nothing to that
    trust (once R7-1 is fixed).

## Findings

### R7-1 (Tier 1, sound; trusted). `OpenBackend`'s restatement is false in two ways, and the duplication also breaks `bootstrapContract`

**The arbitrary `P`.**
- `storage.OpenBackend.spec` quantifies over every `P : BParams` (`Spec/.../storage/OpenBackend.lean:37-47`; the axiom at `Proof/.../storage/OpenBackend.lean:41`).
  `openPre` asks only `P.Wf` and the limit.
- With `bkNoCmp γ := fkOwn γ 0`, the post `⌜noCmpData D⌝ -∗ bkNoCmp γ` claims that `P.FK`'s keys
  are absent. But `noCmpData` is a statement about the two compaction keys only (`Image.lean:48`).
- Take `P.FK n k := (n = "lease")` (allowed by the planned `Wf`) and a `D` with a lease. Then
  `noCmpData D` holds, the axiom gives `fkOwn γ 0`, and the read law then says a lease read is
  empty. That is false of Go.

**The duplication.**
- The plan has `New`/`newBackend` give the creator `fkOwn γ (if fkAbsD P D then 0 else 1)`, and
  `New`'s post is `newPost`/`newPostK`.
- If that half is inside `newPostK`, then `OpenBackend`'s post `newPostK ∗ (⌜noCmpData D⌝ -∗ fkOwn
  γ 0)` holds two client halves of the same `monoNat`, plus the batch lock's half. That is false
  whenever `noCmpData D`.
  - So the axiom becomes false of Go, which does return.
  - Worse, it is a source of `False` after every `OpenBackend` over a clean file. Every server
    result reaches such a call.
- The same happens in `bootOk`. It holds `Hnew : newPost …` (`InvBoot.lean:384`) and also
  `Hncmp : bkNoCmp d.γB` (`:401`). So `bootstrapContract`, the premise of `NewServer.spec`, would be
  unsatisfiable, and the exported server results would become vacuous.
- If instead the half is kept out of `newPostK`, then `OpenBackend` gives nothing when
  `¬ noCmpData D`. A store over a file that already records a compaction could then never write the
  keys again (the wiring step's compaction). Sufficiency fails there.

**Restatement.**
- `newPostK`/`newPost` carry `fkOwn γ (if fkAbsD P D then 0 else 1)`, and `OpenBackend`'s post is
  just `newPostK γ P W Pk K b D`. Drop the wand: the axiom then claims only "does what `New` does".
- mvcc proves a law `bkNoCmp_of : P.FK = cmpFK → noCmpData D → fkOwn γ (if fkAbsD P D then 0 else 1)
  ⊢ bkNoCmp γ`, with `cmpFK` a conjunct of `bridgeParams`.
- `bootOk` replaces `Hncmp` by `⌜noCmpData D⌝`, a pure fact about the fresh file, and
  `bootBackend_of_newPost` derives `bkNoCmp`.
- `SnapApplyWalk.lean:393` does the same through `bkNoCmp_of`.
- The trusted statement's diff is then visible, instead of "same text, new meaning". That phrase
  should not appear in the plan for a trusted statement.

### R7-2 (Tier 1, sufficient). The read law cannot prove the mvcc clause

- The plan's law is `fkOwn γ 0 ∗ rtHeldF γ P b rtx rv p ⊢ ⌜fkAbsRv P rv⌝`.
- The clause it must prove is `□ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok)`. Inside the wand the
  bridge holds `NC` but not `Tok`, and `rtHeldF` is inside `Tok`. `rt_locked`
  (`BackendBridge.lean:1278-1290`) is a persistent statement with no `rtHeldF` in its context.
- **Restatement.**
  - The witness is a persistent part of `rtCore`. Export it as `fkSeen γ P rv := ∃ n0,
    monoNatLb γ.fk n0 ∗ ⌜n0 = 0 → fkAbsRv P rv⌝`, with two laws:
    - `rtHeldF … rv p ⊢ rtHeldF … rv p ∗ fkSeen γ P rv`;
    - `fkOwn γ 0 ∗ fkSeen γ P rv ⊢ fkOwn γ 0 ∗ ⌜fkAbsRv P rv⌝`.
  - `bridge_rt`/`bridge_rt_clean` take `fkSeen` at `RLock` and pass it to `rt_locked` as a persistent
    premise.
- **Why this is sound.**
  - The lower bound says the authority was at least `n0` when `rv` was set.
  - If `NC` (the half at 0) is shown at any later time, the authority is 0 then, so `n0 = 0`, so
    `fkAbsRv rv`.
  - This holds even if `NC` is shown after `RUnlock`, since the conclusion is a pure fact about `rv`.

### R7-3 (Tier 1, sufficient; scope of the list). "`store.restore`'s spec unchanged" is not true, and the list misses about ten statements

**`store.restore` must name `NC`.**
- Its precondition has `mvcc.isKeyBackendG b (bucketView γ) RT WT … (Rb := Rb) (Bt := Bt)`
  (`Spec/.../mvcc/store__restore.lean:69`). With the default, `NC = False`, and the clause gives
  nothing. `restoreView`'s `keyCleanRead` (`InvStore.lean:4465`) is in the same position.
- `restoreView` takes `γ`, so it can pass `NC := kbNoCmp γ.kb γ.bucket` inside its definition.
  `isKeyBackendG` in the spec text cannot: the argument must be written there. Its meaning changes
  for the restore's callers too.
- Consuming `kbNoCmp` stays right: the clause gives `NC` back, and the proof drops it. The plan's
  "wiring step" note (hand it to the store) is a later change.

**Statements the list should name.** T = trusted, E = exported or a premise of an exported result.
1. `storage.OpenBackend.spec` (T), as in R7-1.
2. `storage.OpenSnapshotBackend.spec` (E, derived from 1). Its post repeats the wand
   (`OpenSnapshotBackend.lean:57`).
3. `newPost`, `newPostK`, `backend.New.spec`, `backend.newBackend.spec` (E through the server).
4. `bootOk` / `bootstrapContract`, the premise of `NewServer.spec` (E), as in R7-1.
5. `bridgeParams` (E: it is in `bootOk`, `InvBoot.lean:376`). It gains `P.FK = cmpFK`. Without it,
   the clause cannot be proved over a general `P`.
6. `store.restore.spec`, `store.Restore.spec` (`keyCleanRead b' …`, `store__Restore.lean:126`) and
   `watchableStore.Restore.spec` (`:54`; the root `mvcc.watchableStore.wp_Restore` is E).
   `rangeEvents.spec` (`:41`) only if it defaults.
   - `storeBackend`/`storeBackendT` (`InvStore.lean:3353`) change in their definitions. They are
     used by `NewStore.spec` and `mvcc_NewStore_backend` (E).
   - Whoever proves `storeBackend` for mvcc's assumed backend (`kb = none`) must now prove the
     clause over the opaque `viewNoCmp`. I did not find who supplies it (*uncertain*).
7. `mvcc.UnsafeReadFinishedCompact.spec` and `UnsafeReadScheduledCompact.spec`. They take
   `□ metaReadSpec rt nc` with no token (`UnsafeReadFinishedCompact.lean`).
   - They must gain `Tok` in the pre and post.
   - In the `found` case they also need `rdCap Rd Tok`: `BytesToRev` reads the value's slice, which
     is now lent rather than `↦*□`.
8. `metaReadTx` (and `store.checkPrevCompactionCompleted.spec`, which uses it). This is question 3's
   other half.
   - Its reads at `nc = false` still need the value form (`BParams.VI`, question 4). The design does
     not close that `sorry`. The plan should say so.
9. The `UnsafePut`/`UnsafeSeqPut` specs, as in R7-4. `batchTxBuffered.UnsafePut`'s callers are the
   server's hook (`BackendHooks__OnPreCommitUnsafe`), cindex, schema and the bridges. Each needs
   `fkPut … = True` from `Wf`.
10. Axioms whose meaning moves through `isBackend`/`batchLocked`, and which stay true:
    - `backend.backend.Snapshot.wp_proof` (T; it only commits);
    - `schema.membershipBackend.MustSaveMemberToBackend` (T; its puts are to `members`);
    - `MustUnsafePutLease` and `UnsafeDeleteLease` (T; they take the caller's own triple, so they are
      unaffected).

    Each needs one line in the trust-base note.
11. The exported results that rested on `kbNoCmp_metaNone`: the 21 listed in `nocmpread.md`. Their
    premise `bkNoCmp d.γB` (`Results.lean:825,894,1046`, `StoreBackend.lean:91`,
    `mvcc/Results.lean:266`) stops being opaque.
    - Each must be checked to take no second `fkOwn` beside it (R7-1's duplication).
    - After the change, `etc/tcb-report.py --check --update` drops `mvcc.kbNoCmp_metaNone`
      (`etc/tcb-baseline.txt:570`).

### R7-4 (Tier 1 for the plan, package-internal). The inner `batchTx` puts cannot take `fkPut`

- `batchTx.UnsafePut.spec`/`UnsafeSeqPut.spec` hold only `btW γ t st`: the fields and `ownWTx`
  (`InvBatch.lean:40`). They have no part of the batch lock's ghost.
- Their post `fkOwn γ 1` cannot be proved: raising a `monoNat` needs its whole authority. The
  premise is also unneeded.
- The obligation already arises where it should. `batchTxBuffered`'s wrapper re-folds
  `batchLocked`, whose `batchGhostAt` needs `n = 0 → fkAbsSt` for the new state.
- **Restatement.**
  - The inner specs stay unchanged.
  - `batchTxBuffered.UnsafePut` takes `fkPut γ P bi.name kb`, as planned.
  - `batchTxBuffered.UnsafeSeqPut` takes the pure premise `P.FK bi.name kb = false`. It already
    takes `P.hk … = false` and `P.RB … = false` (`batchTxBuffered__UnsafeSeqPut.lean`), and its
    only callers put into `Key`.

### R7-5 (Tier 2, question 2). The ghost is right; two clauses need their reason stated

- **The ghost is sufficient and close to minimal.**
  - Readers cannot see the batch lock's state, so the reader-side fact needs a persistent witness
    tied to the time `rv` was set. A lower bound on a monotone counter is the standard one.
  - A one-shot (pending/shot) is equivalent. A plain two-halves `Bool` (the axiom review's
    proposal) is not: its readers would have no stable witness.
- **The client's half is a right to write the keys, and the post must give it back.**
  - `∃ v, fkOwn γ v` stays exclusive at 1 too, and the post `fkOwn γ 1` gives it back. That is
    needed: the store writes both keys at every compaction.
  - It matches Go: only the store writes them, `store.go:47,59`.
- **`Wf`'s "an `FK` key is not in a safe-range bucket".**
  - I found no use for it. For `KBReal.P`, `FK ⊆ Meta`, which is a hook bucket, so the clause holds
    anyway.
  - `P.Wf` is a premise of the trusted `openPre` (`InvOpen.lean:84`). State why it is needed or drop
    it ("No constant or conjunct whose reason you do not know").
  - "Not a hook's own key" is needed: it is the bridge's `hHK` moved into `Wf`.
- **"Updated where `safeRv` is".** The places are where `rv` changes: `New`, the `Unlock`'s
  write-back, the commit (`unsafeCommit`), `CommitAndStop`, and `readTx.Lock`'s client re-folding
  `rtRes` (which cannot change `rv`). That is the same set, but name it by `rv`.
- **`ConcurrentReadTx` gets no clause, which is right.** Its `keyReadLocked` has `rng = false`, and
  its cached copy is a past state in `H` with no recorded lower bound. If it is ever needed, record
  `fkSeen` in `histAt`.

### R7-6 (Tier 2, question 3). The default `NC := False` is not a second family, but drop it

- **Why it is not a family.**
  - It is one definition. `NC := False` is an instance, and a weakening law `NC ⇒ False` is trivial.
  - `isKeyBackendG` already defaults `Req`, `Rb`, `Bt`, `SR` and `SRh` (`InvStore.lean:1299-1305`).
  - There is a single proof per bridge, at the real `NC`. So the one-spec rule is kept, as long as
    no bridge or store theorem is ever proved twice, once per `NC`.
- **Why to drop the default anyway.**
  - A defaulted argument is invisible at the use site, and possibly in `interface/` (*uncertain*: I
    did not check `gen-interface.py`'s rendering of defaulted arguments).
  - R7-3's restore is exactly the case where the default silently gives the useless instance.
  - Write `NC` explicitly in every statement. A consumer that ignores it quantifies over it, or takes
    `keyReadLocked_noNC`.
- **The clause's shape is sound** (see What is good) **and usable** by `store.restore` through
  `wp_apply (hFin rt true)` with `Tok`, once R7-2's witness and item 7's token are in.
  `store__restore.lean:85` and `:596` become two `ihave`s from `Hlk`.

## Go code

No bug found.
- Candidate checked: does the fork's non-blocking defrag (`backend.go:694-790`, `catchUpDefrag`
  `:960-1032`) resurrect keys that are deleted during its bulk copy?
- It does not. Phase 1 copies only safe-range buckets, and safe-range deletes are excluded for the
  whole call.
- No `issues/` entry concerns it.

## Ranked by need of revision

1. **R7-1**: the `OpenBackend` axiom (T), `newPost(K)` and `bootOk`. Without the fix the design
   adds a false axiom and makes `NewServer`'s premise vacuous.
2. **R7-3**: the list of statement changes, including `store.restore`'s precondition and the
   exported `Restore` specs.
3. **R7-2**: the read law's shape (`fkSeen`).
4. **R7-4**: the inner `batchTx` puts, and `UnsafeSeqPut`'s premise.
5. **R7-6**: drop the default `NC`.
6. **R7-5**: state the reasons for `Wf`'s safe-range clause and for the update points.

## The working tree at review time (uncommitted; not reviewed as statements)

The author was already drafting while this round ran: 16 files modified and `FkLemmas.lean` new,
none of it committed. Measured against the findings:

- **R7-1, arbitrary-`P` half: addressed in the draft.**
  - The draft fixes the keys instead of adding a parameter: `Model2.lean`'s new `fkKey`, which is
    `meta` together with the two compaction keys.
  - So `fkAbsD D ↔ noCmpData D` for every `P`. `BParams.FK` is gone, and with it the `KBReal.P`/`Wf`
    clauses and R7-5's question about the safe-range clause.
  - The duplication half (`newPost`/`newPostK`, `OpenBackend`, `bootOk`) stands: `InvNew.lean` is
    not yet touched.
- **R7-2 stands.**
  - The draft's persistent `fkRd γ P rv` (in `rtCore`) is exactly the witness needed.
  - But the only law exported is `rtHeldF_fk : fkOwn γ 0 ∗ rtHeldF … ⊢ … ∗ ⌜fkAbsRv P rv⌝`
    (`ReadLemmas.lean`, diff). That is the plan's shape, and it needs `Tok` inside the clause.
  - Add `rtHeldF … ⊢ rtHeldF … ∗ fkRd γ P rv` and `fkOwn γ 0 ∗ fkRd γ P rv ⊢ ⌜fkAbsRv P rv⌝`.
- **R7-4: addressed in the draft.**
  - The inner `batchTx` specs are untouched.
  - `batchTxBuffered.UnsafeSeqPut` takes `¬ fkKey bi.name kb`.
  - `batchTxBuffered.UnsafePut` takes and returns `fkPut γ bi.name kb`.
- **R7-3 and R7-6** concern files the draft has not reached yet.
