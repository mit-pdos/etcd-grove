# Review: mvccfull F1's mvcc API candidates, round 1 (2026-11-09)

Commit under review: `a4c071c7dd` (branch `worktree-mvcc-full-tester`). Judged by
`.claude/skills/spec/PRINCIPLES.md` and the examples `restore-modes.md` and `apply-loop-merge.md`.
I checked all six draft files with `etc/lean-check.py -a`. They typecheck with 0 errors. The only
`sorry`s are the corollaries and the glue in `NewStoreR`, `newWatchableStoreR` and `NewR`.

The Go is etcd at the pin, under `/home/ubuntu/.claude-F/jobs/fa46cf72/tmp/srv/`. Below,
`kvstore.go` means `storage/mvcc/kvstore.go`. I found **no bug in the Go code**, so nothing goes to
`issues/` or `nonissues/`.

## Ranking (need of revision)

1. `ApiNewRestoring.lean` (`New.specR`, `NewStore.specR`): one first-tier finding (F1.1) and three
   second-tier ones.
2. The internal chain (`NewStoreR`, `newWatchableStoreR`, `NewR`): one first-tier finding (F2.1)
   and two second-tier ones.
3. `ApiErrVars2.lean` (`errVars2.law`): second-tier only (F3.1, F3.2).
4. `ApiWatchR.lean` (`Watch.contractR`): one small second-tier fix (F4.1).

---

## 1. `ApiNewRestoring.lean`: `New.specR`, `NewStore.specR`

**Good.**

- **One statement covers the fresh and the restored storage.** It reuses `Restore`'s vocabulary
  word for word: `mvccStorageFor`, `storageHook`/`hookRun`/`storageReq`, `leaseOwn`, `pendItems`,
  and the item premise of `KV.Restore.contract` (Api.lean:606-626). So there is no new storage
  abstraction, and the coupling to `lease` is unchanged.
- **True of the code.**
  - `NewStore` runs the same `s.restore()` as `Restore` (kvstore.go:126-131, 313; `restore` at
    317-426).
  - Neither panic is reachable under the pre. `panic("failed to recover…")` cannot happen because
    `restore` always returns `nil`. `panic("no lessor to attach lease")` (l.394-396) is excluded
    because `isLessor le γl` gives a non-nil `le`.
  - `Attach` errors are only logged (l.398-405). The premise `lid ∈ Ls` with `leaseOwn` (exclusive,
    lent) makes each `Attach` succeed, so the post's `pendItems σ.log []` holds.
  - On a resume (`u`), the resources `newResumePre` takes are used synchronously, once:
    - `compactLockfree` → `updateCompactRev` (l.262-269, 197-222);
    - `SetScheduledCompact` uses `LockInsideApply`, which runs the hook (store.go:38-42);
    - then `ForceCommit` runs (l.216).
  - The asynchronous job (`scheduleCompaction`) uses `LockOutsideApply` (kvstore_compaction.go:56),
    so the hook does not run twice.
  - `restore`'s clamps (l.372-391) rule out `ErrCompacted` and `ErrFutureRev` on the resume.
- **Gating the hook and the commit request by `u` fits both new clients.** Both set the hook only
  after `New`:
  - the server: server.go:366 (`New`), then l.409 (the hook set);
  - the tester: mvccfull.go:496-497.
  So both lend `storageHook B _ nil` only when `u`, and get it back.

**F1.1 (first tier, a decision and an explicit list are needed before Freeze): the old `New.spec`
and `NewStore.spec` are not instances, and exported statements change.**

- **Principle.** One spec per function: a variant is fine only as a corollary of the one proof
  (`apply-loop-merge.md`: the restoring corollary states the old spec exactly).
- **What breaks.** `New.specR` takes `lease.leaseOwn γl Ls ∅`, which `New.spec` (Api.lean:956-971)
  does not hold. So `New.spec` cannot be derived, and the file states no corollary. The docstring's
  "At σ = mvccStart, u = false: today's New.spec" is therefore inexact.
- **Callers that need a different statement:**
  - **Proofs (cheap, a line or two each):**
    - `NewServer.lean` l.845: it holds `Hlown` from l.724 until l.2599.
    - mvccrand `runChecks.lean` l.172.
  - **Exported theorems, whose statements must change.** Their preconditions do not hold
    `leaseOwn`, so each gains `lease.leaseOwn γl [] ∅` in pre and post:
    - `server_kv_backend` (etcdserver/Results.lean:914);
    - `server_kv_watchable` (:973);
    - `server_kv_backend_hooks` (:1103);
    - `mvccApi_New_wp_proof` / `mvccApi_NewStore_wp_proof`, which are re-stated
      (ApiResults.lean:103-108).
- **The gap in the plan.** The plan's Freeze row 1 says only "callers move (… server results)".
- **Restatement.** Add `New.spec_of_specR` / `NewStore.spec_of_specR`, stated as
  "`New.spec` with `leaseOwn γl [] ∅` lent and given back", as the internal files do. List the three
  exported theorems on the Freeze list as statements that change.
- **The alternative.** Make the lease part conditional (`if pendItems σ.log [] = ∅ then True else
  leaseOwn …`). It gives an exact instance, but the statement gets uglier and the proof needs a
  branch. I recommend lending: every caller holds the part, and the restore loop's proof is uniform.
  Put the choice to the user.

**F1.2 (second tier): pure premises written as Lean implications.**

- **Principle.** Pure premises go in the precondition; convert one when you change it.
- **What the draft does.** It adds `MvccReachable σ → σ.pending = none →` before the triple, next to
  `batchLimitOk →`. `KV.Restore.contract` has the same facts as `⌜MvccReachable σ' ∧ σ'.pending =
  none⌝` inside its pre.
- **Restatement.** Put `⌜batchLimitOk cfg.CompactionBatchLimit' ∧ MvccReachable σ ∧ σ.pending =
  none⌝` inside `{{ … }}`.

**F1.3 (second tier): two new helper definitions hide part of the statement.**

- **Principle.** No helper definition that hides part of the statement (`put.md`, critique 2). The
  measure is the API's count of abstractions.
- **What the draft does.** `newResumePre` and `newResumePost` are new public `def`s. `KV.Restore`
  writes the same resources inline, with `(if u then iprop(Post ∗ Y) else iprop(Pre ∗ X))`.
- **Restatement.** Inline both:
  - pre: `(if u then iprop(storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗ Pre ∗ hookRun
    Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y) else iprop(True))`;
  - post: `(if u then iprop(storageHook B dq f ∗ Post ∗ Y) else iprop(True))`.
- **Or,** if a shared definition is wanted, `Restore` should use it too, so the two read alike.

**F1.4 (second tier, know the margin; whether a caller needs it is uncertain): the post has no
receipt of the restored history.**

- **The sibling gives it.** `KV.Restore.contract` hands the update `⧖ (logCh σ'.log)`
  (Api.lean:595-597, 619), "as at every step that changes the history". The receipt is what a
  client's history model needs (`Txn.End`'s docstring, Api.lean:729: client/v3's `kvLogOk`).
- **The client cannot get it elsewhere.** `New.specR` consumes `mvccStorageFor`, and no law
  extracts the receipt from it or from `mvccImage` (both sealed: Api.lean:381-392,
  EtcdBackend.lean:94). So a restarted server whose KV model needs the receipt cannot get it after
  `New`.
- **Restatement.** Add `⧖ (logCh σ.log)` to the post. It is persistent and the proof has it.
- **Not verified:** whether R2d'b's B5 needs it.

**Completeness, per caller.**

- **The tester, `runner.open`** (Spec `runner__open.lean`; proof outline `runner__open.lean`:3-10):
  - Every conjunct of the pre has a source:
    - `mvccStorageFor` from `etcdStorage_open.law` at the file's `mvccImage`;
    - `leaseOwn γl Ls ∅` and the items from `NewLessor.specR`;
    - when `u`: the unset hook, `Pre := True`, `Q' := Pk`, `X := True`;
    - `storageReq B Pk True True` through `etcdStorage_req` and the backend's `commitReq`, as
      mvccrand does at `Pk = True` (writer__run.lean:191).
  - Uncertain: building `commitReq` at mvccfull's own `Pk`, if that is not `True`.
  - The post gives the `Rev` and `FirstRev` checks (mvccfull.go:498-500) what they need:
    `mvccState γ σ`, and on a resume the scheduled revision is `σ.crev`, which is
    `compactMainRev` after `updateCompactRev` (l.211).
- **The server's restart (B3/B5):**
  - The hook is `nil` at `New` (server.go:366/409).
  - `storageReq … True True` is built the same way at the snapshot path
    (EtcdServer__snapshot.lean:273).
  - `MvccReachable σ` comes from the server's model, as for `Restore`.
  - `leaseOwn` comes from the restated `NewLessor`.
  - The only open question is F1.4.

## 2. The internal chain: `NewStoreR.lean`, `newWatchableStoreR.lean`, `NewR.lean`

**Good.**

- **The mode-indexed shape follows `restore-modes.md`:** `restoreImageM`, `restoreRcptM`,
  `resumeCtxM`/`resumeBackM`, `storeCloserM`/`wsCloserM`. Off, `restoreImageM` forces
  `r = CmpRecs.empty` (RestoreVocab.lean:177-190), so the post's `crevUB ½ (-1)` off is consistent
  with `storeCloserM … r.crev`.
- **The permits of both records are taken**, as amendment 1 of that example requires: `restore`
  writes `compactMainRev` from the finished record, then `compactLockfree` writes the scheduled one.
- **Dropping `kb = none` is fine.** It is internal (Scope), and no linked result reaches `NewStore`
  at `none` (Link.lean:616-617; `StoreBackend.lean` is at `some d`).

**F2.1 (first tier for the internal text; the API text is unaffected): the clean-read premise is
not, as written, what its one caller's outline can supply.**

- **Principles.** Complete; every premise has a source.
- **What the pre takes.** `RC` on its own, the clean read
  `keyCleanReadR b (bucketViewC γ) (storeRT γ ∗ RC) (kbRecs …) r`, and the whole
  `restoreImageM d γb L' r`.
- **What the glue's outline says.** `NewR.lean`'s glue, step 4, says `RC` must be the evidence that
  nothing was deleted since the open: the `kbVals … ∅` part that `restoreImageM` carries
  (RestoreVocab.lean:170-182). "So `RC` would be lent out of the image, the proof of `NewStore`
  splitting it off".
- **The conflict.** If so, `api.New.specR_of_internal` cannot supply both `RC` and the whole
  `restoreImageM`. The text and its outline disagree.
- **Restatement**, one of:
  - (a) Drop the separate `RC`. Let the clean read's read token carry the part of `restoreImageM`
    that the proof splits off, and give `restoreImageM` back only in the form the post needs.
  - (b) Prove the R1 bridge lemma first (the plan's Probe) and fix the text to what it needs.
- **Either way,** do not freeze the internal `NewStore.specR` before R1.

**F2.2 (second tier): the `spec_of_specR` corollaries are new statements, not today's specs.**

- **The corollaries.** They add the clean read, `RC` and the lessor's part, and change the post
  (`storeCloserM`/`wsCloserM` on, `hookP` for `hookInit … f`). So today's internal
  `mvcc.NewStore.spec`, `newWatchableStore.spec` and `New.spec` stop being proved.
- **Who must be re-proved:** `NewStoreApi`, `NewApi`, the proof of `newWatchableStore`, and
  `StoreBackend.lean`'s `mvcc.NewStore_backend` (l.64ff).
- **`NewStore_backend`'s own statement changes.** Its pre (l.93-106) has neither `leaseOwn` nor the
  clean read, and its post's `hookIs γ Pk #f` must now come from `hookP`.
- **Restatement.** Say so on the Freeze list ("internal statements re-stated: …"), and drop the
  corollaries no caller will use.

**F2.3 (second tier): pure premises as implications.** `batchLimitOk → restoreLogOk R →` in all
three files: as F1.2.

**Notes (not findings).**

- **The certificate premise.** Its three-way disjunction has a reason (`certOk`'s shape), and the
  glue uses only its third disjunct (`M = {0 ↦ []}`).
- **The permit disjunctions** `(⌜r.finRev = -1⌝ ∨ □ Perm r.finRev)` inline `crevPermAt`'s shape
  because `γ` does not exist yet. That is acceptable.
- **A point for the proof, not a data race.** In `newWatchableStore`, a resumed job is already
  queued when `s.store.ReadView/WriteView` are overwritten (watchable_store.go:97, 103-104). The job
  does not read those fields, so there is no race. The proof of `newWatchableStoreR` must still keep
  the job's share of the store apart from `fieldShare`.

## 3. `ApiErrVars2.lean`: `errVars2.law`

**Good.**

- **True.** The four variables are separate `errors.New` allocations with distinct literal messages
  (kvstore.go:38-39, watcher.go:30-31), and `errVarApart_of` (Proof/errors/NewVarCell.lean:107) is
  the right argument.
- **The `mvccInit` change is correctly described.** I counted the 42 conjuncts (Base.lean:222-265):
  the `errorsNewVar`s are at 31-33 and the cells at 35-36. Every destructuring I checked ends with
  `-` (apply/Init.lean:193, v3rpc/Init.lean:333, ServerKVOn.lean:813-814), except the one the draft
  names (store__setupMetricsReporter.lean:32-33).
- **It gives the tester both facts it lacks:** `ErrWatcherNotExist` for `Cancel`, and
  `ErrCompacted` apart from `ErrFutureRev` for `checkStoreRange` (mvccfull.go:1055).

**F3.1 (second tier): the apartness is indexed by messages, which a client must restate.**

- **Principles.** The vocabulary is part of the spec; caller burden.
- **The burden.** The client thinks in the variables, but to use the law it must spell out both
  message literals and prove list membership: `compacted_ne_future` takes four lines per pair.
- **Restatement.**
  `□ ∀ X Y, ⌜X ∈ [ErrCompacted, ErrFutureRev, ErrEmptyWatcherRange, ErrWatcherNotExist] ∧ Y ∈ […]
  ∧ X ≠ Y⌝ -∗ errVarApart X Y`, or the six pairs as conjuncts. The proof is the same (the messages
  are pairwise distinct), and `errVarMsgs` leaves the API.

**F3.2 (second tier): two laws for one fact family.**

- **Principle.** After a change, drop what existed only for what it changed.
- **What the draft does.** It keeps `errVars.law` as a corollary (`errVars_of_errVars2`).
- **Restatement.** Replace `errVars.law` by `errVars2.law` and add a trailing `-` at its callers:
  - mvccrand: checkRange.lean:97, watchCheck__register.lean:42;
  - mvccfull: runner__checkStoreRange, runner__compact, runner__endEpoch, stream__cancel,
    stream__watch, stream__act.

**Notes (not findings).**

- `apply/Init.lean:193`, `v3rpc/Init.lean:333` and `ServerKVOn.lean:813` unfold mvcc's package fact
  from outside the package. That is a known defect from before this change: one missing law per
  unfold. A later change could serve them from this law, adding `ErrWatcherDuplicateID`, which
  v3rpc uses.
- `errVars2.law_of_ext`'s positional destructuring belongs in the package's `Proof/` file at
  landing, not in the API's `Spec/` file (the layout rule).

## 4. `ApiWatchR.lean`: `WatchStream.Watch.contractR`

**Good.**

- **True.** The range check is the first statement (watcher.go:118-120), before the lock (l.122).
  Only `key`, `end` and their contents are read on that path. `len(end) != 0 ∧ Compare != -1` is
  `e ≠ [] ∧ ¬ GoStringLt kk e`, and the proof's branch already exists
  (watchStream__Watch.lean:84-96).
- **A case split on the input, not a disjunction of specs.** `contract_of_contractR` is proved, so
  every caller is unchanged.
- **It lets mvccfull's `Watch(k, k)` check** (mvccfull.go:1263-1265) and mvccrand drop the
  vacuous-update workaround (`register_au_empty`, WatchLock.lean:476).

**F4.1 (second tier): the empty branch's give-back `(⌜empty⌝ ∨ au)` carries no information.**

- **Principles.** No vacuous guarantee; after a change, drop what existed only for it.
- **Why it says nothing.** The branch already states `empty`, so the left disjunct is always true. A
  caller who passed `au` cannot get it back from the disjunction. The docstring's "gives back what it
  was given" misleads, and `contract_of_contractR` already frames `au` around the call instead.
- **Restatement.** The left branch becomes `⌜e ≠ [] ∧ ¬ go.GoStringLt kk e ∧ id = W64 (-1)⌝ ∗
  globalAddr ErrEmptyWatcherRange ↦□ err`.

**Notes (not findings).**

- **Change the rest with it.** The `isWatchStream` bundle, `watchStream.Watch.spec` and the proof of
  `shapes.law` change with the contract. mvccrand's `register_au_empty` can go.
- **A tester premise, not the spec's.** The tester's empty-range check needs `genKey` non-empty: at
  `k = ""`, `Watch(k, k)` has `len(end) = 0` and registers a watcher.

## First-tier findings, in one list

- **F1.1:** decide between lending `leaseOwn` (recommended) and a conditional lease part. Add
  `New.spec_of_specR` and `NewStore.spec_of_specR`. List the exported statements that change
  (`server_kv_backend`, `server_kv_watchable`, `server_kv_backend_hooks`, and the re-stated API
  results) on the Freeze list.
- **F2.1:** reconcile the internal `NewStore.specR`'s `RC` and clean-read premise with the glue's
  outline (R1) before freezing the internal text.
