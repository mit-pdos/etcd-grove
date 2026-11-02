# backend-cmp, Review round 9 (2026-10-29): round 8's repairs

**Under review.** Commit `aa2dcdcac0` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`; it is
`HEAD` at review time, with a clean tree). Diffed against `2e49ff1aa9`. This round judges the
implemented statements, not the plan text.

**Read.**
- The diff.
- `InvStore.lean`: `bkNoCmp`, `viewNoCmp`, `kbNoCmp`, `kbMW` (`:471-495`); `metaPutCap` (`:1071`);
  `batchTxSpecG` (`:1105-1222`); `batchTxInitSpec` (`:1243`); `isBatchTxG`, `batchTxSpec`,
  `isKeyBackendG` (`:1340-1392`); `isKeyBackendG_cmp`, `physOk`, `storeBackend(T)`, `kbCmp`/`storeCmp`
  (`:1659`).
- `BackendBridge.lean`: `bt_metaPut` (`:2221`), `isKeyBackendG_of_backend` (`:2365`),
  `isKeyBackendG_of_backendC` (`:2630-2749`), `storeBackendT_of_backend`.
- `Results.lean`: `mvcc_backend_bridge`.
- `Image.lean` (`bkNoCmp_of_fkOwn`), `InvBackend.lean` (`fkOwn`, `fkPut`, `rtCore`), and
  `batchTxBuffered__unsafeCommit.lean:259`.
- The specs `store.restore`, `rangeEvents`, `NewStore`, `New`, `newWatchableStore`,
  `store.Compact`, `store.updateCompactRev`, `SetScheduledCompact`, `UnsafeSetFinishedCompact` and
  `schema.MustUnsafeSaveConfStateToBackend`.
- The changed proofs: `scheduleCompaction`, `Set*Compact`, `NewStore`, `store.Restore`, and
  `storeTxnWrite.*`.
- Go at the pin: `server/storage/mvcc/store.go:23-59`, `kvstore.go:327-342`, and
  `schema/bucket.go:82-83`. A grep of the tree for every use of the two key names finds only
  `store.go:47,59` writing them, plus `tools/etcd-dump-db` reading them.

**Build.** The background build of record ends with `Build completed successfully (10943 jobs)`,
exit 0 (the tail of `be-r8-build.log`; the log was written after the commit's timestamp). I did not
build anything myself.

## Summary

- **No Tier-1 finding.** R8-1 is fixed, and no other `Meta` put in mvcc's contract bypasses `MW`.
- **R8-2's mechanical part is done.** `MW` has no default on `batchTxSpecG`, `isBatchTxG` or
  `isKeyBackendG`. The store names it `kbMW γ.kb` everywhere it names `kbNoCmp`.
- **The agent's choice `kbMW none := True` is acceptable as an interim. It is not unsound** (R9-2):
  - No statement is false, and no axiom is added.
  - Over the real backend, a client can write a compaction key only with the flag's half.
  - No exclusive token is held twice.
  - Its cost is vacuity over `kb = none`. That vacuity already existed in Lean before the change
    (`viewNoCmp` is `opaque`, and nothing supplies it). The cost should be stated more sharply: the
    store's compaction specs are proved only over `kb = none`.
- **Two Tier-2 items:**
  - R9-1: the main docstrings of `batchTxSpecG` and `isKeyBackendG` do not mention `MW`.
  - R9-3: `Set*Compact.spec` are pinned to the assumed instance; this is a known part of the wiring
    step.
- **R8-1 to R8-5 are all fixed or recorded.**
- **Stop rule:** no first-tier finding is churn from round 8's repair. The increment has not drawn a
  first-tier finding three rounds running. This round ends the increment's review.
- **No Go bug.**

## What is good

### R8-1's fix is right, and it is the only route that needed it

- **The clause.** The compacting range's clause now gives
  `□ ∀ n, metaPutCap bt iprop(U (n + 1) ∗ MW) iprop(U n ∗ MW)` (`InvStore.lean:1206`).
- **Over the real backend the `sorry` is provable again** (`isKeyBackendG_of_backendC`,
  `BackendBridge.lean:2701`, `MW = ∃ f, fkOwn γ f`, `:2647`):
  - `batchTxBuffered.UnsafePut` at an `fkKey` takes `fkPut γ "meta" k = ∃ f, fkOwn γ f` and gives
    it back. That is exactly `MW`, threaded through.
  - `bt_metaPut` (`:2221-2235`) already does this for the fresh-session clause.
- **I enumerated every way the contract lets a client reach `UnsafePut` on `Meta`,** and each needs
  `MW` or cannot hit a compaction key:
  - `metaPutCap` is the only shape of a `Meta` put in mvcc's contract, and only two clauses produce
    one: the step put (`:1206`) and the fresh-session put (`:1213-1214`). Both now carry `MW` on
    both sides.
  - `UnsafeSetFinishedCompact.spec` and `UnsafeSetScheduledCompact.spec` take a `metaPutCap` from
    their caller with free `X`/`Y`. They add no route.
  - `UnsafeSeqPut` (`:1167`) is pinned to `globalAddr schema.Key ↦□ b`. Over the real backend it
    takes `¬ fkKey bi.name kb`, and `"key"` is not `"meta"`.
  - `UnsafeCreateBucket` (`batchTxInitSpec`, `:1247-1251`) creates `Key` or `Meta` but writes no
    keys. `fkAbsSt` is kept by bucket creation (round 8, `FkLemmas.lean`).
  - The deletes (`Key` under `Del`, `Lease` under `Rb`) cannot make a key present.
  - The hooks (`bkHookIs`) write only `P.hk` keys. The C bridge's `hHK` premise excludes the
    compaction keys from them, and `UnsafePut` would require `fkPut` anyway.
  - Outside mvcc's contract, the axioms that put into the backend do so through the caller's own
    triple, at keys that are not `fkKey`:
    - `schema.MustUnsafeSaveConfStateToBackend` (`Meta`/`confState`; the spec takes the caller's
      `UnsafePut` triple). Round 8's trust-base list missed it, but it needs nothing.
    - `MustUnsafePutLease` and `UnsafeDeleteLease` (the `lease` bucket).
    - `MustSaveMemberToBackend` (the `members` bucket).
  - Go agrees: the only writers of the two keys are `store.go:47,59`. They are reached from
    `SetScheduledCompact` (`kvstore.go:213`) and from the job (`kvstore_compaction.go:70`).
- **`NC` and `MW` stay exclusive.** Both are the client's half of `γ.fk`
  (`fkOwn := monoNatAuthOwn γ.fk ½ n`, `InvBackend.lean:289`), and the lock invariant holds the
  other half. So a client holds at most one of them.
  - A client holding `NC` may spend it as `MW` (`f = 0`) to put a key.
  - It gets back `∃ f, fkOwn γ f` and can no longer produce `fkOwn γ 0`.
  - No law in the API lowers the flag. `bkNoCmp_of_fkOwn` (`Image.lean:65`) needs `noCmpData D` at
    `fkInit D`, which happens only at the backend's creation.
  - So the reader's clause `□ (NC -∗ NC ∗ □ metaReadSpec …)` cannot be invoked after such a put.
    This closes round 8's attack (put, unlock, then read under `NC`).

### `MW` is explicit, and the instances line up

- **`kbMW`** (`InvStore.lean:492`) is `∃ f, backend.fkOwn d.γB f` for `some d` and `True` for
  `none`. It sits next to `kbNoCmp`, `kbRb` and `kbBt`, and it appears in:
  - `physOk` (`:2815`), `storeBackend` (`:3418`) and `storeBackendT` (`:3433`);
  - the `#Hbt` facts of `storeTxnWriteIs` and `storeTxnWriteCore` (`:3951`, `:3997`);
  - `batchTxSpec` (`:1296`).
- **The bridges' exports agree with `kbMW (some d)`:**
  - `isKeyBackendG_of_backend` (`:2397`, `Cmp` false, so both clauses are vacuous there);
  - `isKeyBackendG_of_backendC` (`:2647`);
  - `mvcc_backend_bridge` (`Results.lean:229`);
  - `storeBackendT_of_backend`, which closes by `simp only [kbWi, kbNoCmp, kbMW]` (`:2814`).
  - A wiring that passed the wrong `MW` would not type-check.
- **`isKeyBackendG_cmp`** (`:2324-2330`) converts the store's contract at `storeCmp γ` (so
  `γ.kb = none`) to `MW := kbMW none`. That is the same term after the rewrite, so no strength is
  lost.
- **`store.restore.spec` and `rangeEvents.spec` quantify `MW` universally.** That is the right
  generality: neither function puts, and each caller passes its own instance's `MW`.
  - `NewStore.lean:383` passes `kbMW γ.kb`.
  - `store__Restore.lean:202` passes `kbMW (γ.withPhys p').kb`.
  - `restore` still consumes `kbNoCmp γ.kb γ.bucket` and reads through the reader's clause
    (`store__restore.lean:89,601`), as Go's `restore` does (`kvstore.go:327-342`).
- **The callers' burden is mechanical:**
  - one positional `_` (`storeTxnWrite__End.lean:39`);
  - `(mvcc.kbMW γ.kb)` in the `ihave #Hbt0` restatements;
  - `unfold mvcc.kbMW; itrivial` where the assumed instance frames `True`
    (`SetScheduledCompact.lean`, `SetFinishedCompact.lean`, `store__scheduleCompaction.lean:560-566`).

### The docs (R8-4) and the decision (R8-3)

- **"Raised" is gone** from `fkPut`'s docstring (`InvBackend.lean:306-308`) and from `UnsafePut`'s
  (`Spec/.../batchTxBuffered__UnsafePut.lean:33-35`). Both now say "at some value", and that the
  post omits the code's `≥ 1`.
- **`rtCore`'s docstring traces `CommitAndStop`.** I checked it: `unsafeCommit`'s stop branch is
  `rtRes_cm_close … true Loc.null …` (`batchTxBuffered__unsafeCommit.lean:259`).
- **The trust-base lines** for `Snapshot`, `MustSaveMemberToBackend` and the lease axioms are in the
  plan. `MustUnsafeSaveConfStateToBackend` belongs with them; see R9-1.
- **`fkKey` is recorded** in `notes/decisions.md`, "The compaction keys tracked inside the backend",
  with the reason (R7-1's false axiom under a `P.FK`), the cost (R8-3) and how to supersede it.

### Trust base

- No line added in the `.lean` diff contains `sorry`, `axiom`, `opaque` or `admit`. The only match
  is a docstring that mentions an "opaque `viewFk`".
- `etc/tcb-baseline.txt` and the collections are unchanged. The two Draft `sorry`s at
  `BackendBridge.lean:2701,2749` are the same as before.
- The `sorry` at `:2701` is now a provable obligation again, where in round 8 it was impossible.

## Findings

### R9-1 (Tier 2, docs). The contract's main docstrings do not mention `MW`

- **Evidence.** `batchTxSpecG`'s docstring still says that a compaction key is put into `Meta`
  "each from `U (n + 1)` to `U n`" (`InvStore.lean:1125-1132`). Its inline comment (`:1197-1201`)
  says the same.
  - Only the second clause's comment (`:1209-1212`) names `MW`.
  - `isKeyBackendG`'s docstring (`:1340-1356`) never names `MW`, although it is now a required
    argument.
  - A reader of the contract learns what `MW` is only from `kbMW`'s docstring.
- **Who is affected.** Anyone who instantiates the contract (the wiring step, a new backend).
- **Restatement.** In both docstrings, add one phrase:
  > each with the right `MW` to write the compaction keys, given back (the real backend's half of
  > its compaction-key flag, `kbMW`)

  Also add `MustUnsafeSaveConfStateToBackend` to the plan's trust-base list ("a `Meta` put at
  `confState`, the caller's triple, not an `fkKey`").

### R9-2 (Tier 2, scope; the agent's choice for `kb = none`). Acceptable, but say what it costs

- **Not unsound.**
  - `kbMW none := True` adds no false statement.
  - Over the real backend the right is enforced (above).
  - Over mvcc's assumed backend, the contract is only a premise. `viewNoCmp` (`InvStore.lean:475`)
    is `opaque`: no proof can derive anything from it, and no proof can supply it. In Lean, every
    result over `kb = none` that takes `kbNoCmp` was already uninstantiable before round 8.
  - Round 8's opaque `viewFk` would not have changed that in Lean: it would also be opaque, with
    no laws. It would only have made the premise consistent in a model where `viewFk := fkOwn`.
  - The price of `viewFk` is real. The store's compaction proofs (`SetScheduledCompact` in
    `updateCompactRev`, the job's `UnsafeSetFinishedCompact`) would need the store to hold `MW`.
    `store.restore` consumes `kbNoCmp`, so it would have to hand the half to the store instead.
    That changes `restore`'s spec and its callers' (`NewStore`, `store.Restore`, the server's
    `SnapApplyWalk`), and it is the user's question 5. Deferring it is reasonable.
- **What the docstring understates.**
  - The compaction specs need `storeCmp γ`:
    - `store.Compact.spec` (`Spec/.../store__Compact.lean:62`);
    - `store.updateCompactRev.spec` (`:42`);
    - `scheduleCompaction`, through `isKeyBackendG_cmp`.
  - `storeCmp γ` is `kb = none` (`InvStore.lean:1659-1662`).
  - Every `isStore` with `kb = none` comes from `NewStore`, `New` or `newWatchableStore`. All three
    take `kbNoCmp kb γb` (`NewStore.lean:91`, `New.lean:39`, `newWatchableStore.lean:43`), which is
    `viewNoCmp` at `none`.
  - So **the store's compaction results currently describe no backend at all.** Over `kb = none`
    they are vacuous: the premise cannot be supplied, and with `MW = True` it is inconsistent with
    the reader's clause in any model where a creator could hold it. Over `kb = some d` they do not
    apply, because `Cmp` is false.
  - This is not new: before the stage it rested on the false axiom. But it is the fact the user
    needs for question 5. `kbMW`'s docstring says only "results over it that take `kbNoCmp` are
    vacuous".
- **Restatement (docs only).** Extend `kbMW`'s docstring and the plan's R8-2 entry:
  > Until the wiring step, the store's compaction specs (`store.Compact`, `updateCompactRev`,
  > `scheduleCompaction`; `storeCmp`, so `kb = none`) are proved only over this instance, so they
  > hold of no backend yet; the real backend's (`isKeyBackendG_of_backendC`) awaits its two `sorry`s
  > and the store holding `MW`.

  Do not let STATUS count the compaction as verified until then.
- *Uncertain:* the strict claim "no honest creator" in round 8 and in the plan. A creator could
  make `viewNoCmp` exclude the lock tokens, so that its holder can never put. I did not try to
  build such an instance. The vacuity claim above does not depend on it.

### R9-3 (Tier 2, scope; known). `Set*Compact.spec` are pinned to the assumed instance

- `SetScheduledCompact.spec` takes `mvcc.batchTxSpec` (`Spec/.../SetScheduledCompact.lean:32`),
  which is `MW := kbMW none` (`InvStore.lean:1296`). `SetFinishedCompact.spec` does the same.
- Their proofs frame `True` for `MW`.
- Over the real backend these specs must take a general `MW`, and the caller must hold it. This is
  the plan's wiring step, which the plan names, so it is not a defect now.
- It is listed so that question 5's answer covers these two specs as well as `store.restore`.

## R8 findings: status at `HEAD` (`aa2dcdcac0`)

- **R8-1: fixed.** The step put carries `MW` (`:1206`). The `sorry` at `BackendBridge.lean:2701` is
  provable again by `bt_metaPut`'s pattern over the job's own token. The plan names both `Meta`
  clauses as unused by a proved real-backend store.
- **R8-2: fixed (the default is dropped, and `kbMW γ.kb` is named).** The `kb = none` part was
  decided by the agent, not as round 8 suggested. That choice is acceptable (R9-2), with a sharper
  statement of its cost.
- **R8-3: recorded** (`notes/decisions.md`).
- **R8-4: fixed.** `ConfState` is missing from the trust-base list (R9-1, cosmetic).
- **R8-5: noted** under question 4. It was a suggestion.

## The stop rule (`notes/spec-first-plan.md`, "When to stop iterating")

- **Churn.** This round has no first-tier finding, so none is churn from round 8's repair.
  - The repair's new statements (the step put's `MW`, `kbMW`, the `MW` binders on `store.restore`
    and `rangeEvents`) are each true and usable.
  - Its new burden is mechanical.
- **Three rounds running.** The increment is the compaction keys' tracked absence (rounds 7, 8 and
  9).
  - Round 7 had first-tier findings on the plan's statements: `OpenBackend`, the read law,
    `restore`'s list, and the inner puts.
  - Round 8 had one, on `batchTxSpecG`'s step put.
  - Round 9 has none.
  - No statement drew a first-tier finding three rounds running. `batchTxSpecG` drew one only in
    round 8.
- **Recommendation.** Stop reviewing this increment.
  - What is left is the user's: question 5 (does the store hold `MW`, and does `restore` hand the
    half over; this covers R9-2 and R9-3) and question 4 (`BParams.VI`, R8-5).
  - The rest is the glue against the real caller: the two Draft `sorry`s of
    `isKeyBackendG_of_backendC`.
  - The `axiom` skill check before the freeze does not apply: this commit adds and restates no
    axiom.

## Go code

- No bug found, and no `issues/` entry is needed.
- The only writers of `scheduledCompactRev` and `finishedCompactRev` are `mvcc/store.go:47,59`.

## Ranked by need of revision (two-tier rubric)

No Tier-1 finding. Tier 2:

1. **R9-2:** state the `kb = none` vacuity in terms of the compaction specs it empties. Put it to
   the user with question 5.
2. **R9-1:** name `MW` in the docstrings of `batchTxSpecG` and `isKeyBackendG`; add `ConfState` to
   the trust-base list.
3. **R9-3:** `Set*Compact.spec` over a general `MW`, at the wiring step.

Targets ranked by need of revision:

1. `kbMW` (its docstring) and `viewNoCmp`/`kbNoCmp none`: R9-2.
2. `batchTxSpecG` and `isKeyBackendG` (docstrings only): R9-1.
3. `SetScheduledCompact.spec` and `SetFinishedCompact.spec`: R9-3, deferred.
4. No change needed:
   - `isBatchTxG` and `batchTxSpec`;
   - the bridges (`isKeyBackendG_of_backend(C)`, `mvcc_backend_bridge`, `storeBackendT_of_backend`);
   - `store.restore.spec` and `rangeEvents.spec`;
   - `physOk`, `storeBackend` and `storeBackendT`;
   - `fkPut` and `batchTxBuffered.UnsafePut.spec`.
