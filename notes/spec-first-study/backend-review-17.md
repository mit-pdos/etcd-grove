# Backend-compaction review, round 17: question 5's switch, stages 2-4

Reviewed: `5bc9877936..7deaf43ae3` in `/shared/etcd-grove-be` (commits 162cb871b9, 4094258ae1,
7fd3ac8d28, 7deaf43ae3), read with `git show`/`git diff` (not the working tree). Not built. The build
log (`be-q5s234-build2.log`) ends with `tcb: trust base matches etc/tcb-baseline.txt (765 axioms, 8
sorries)`. `ContractLaws.lean` and the bridge contain no `sorry`.

## Summary

| Target | Tier-1 findings | Preferences / docs |
|---|---|---|
| `mvcc/ContractLaws.lean`: `isKeyBackendG_congrDel` (and `batchTxSpecG_congrDel`, `isBatchTxG_congrDel`) | **1** (F1: its premise cannot be established for the instance it exists for) | P1 (two laws where R4-4 recorded one) |
| `BackendBridge.lean`: `isKeyBackendG_of_backendC` (Cmp-parametrized) and `isKeyBackendG_of_backend` (now a corollary) | 0 | D1 (stale docstring), P2 |
| `InvStore.lean`: `viewFk`, `viewNoCmp := viewFk γb 0` | 0 | D2 (stale `kbMW` docstring) |
| `backend.newPost`/`newPostK` with `srSlot b`; `newBackend`'s proof; `storage.OpenBackend` (axiom) | 0 | M1 (margin: defrag's side of the mutex), M2 (axiom check still owed) |
| `SnapApplyWalk`/`BootBackend` pattern fixes | 0 | none |

Ranked by need of revision: **(1) `isKeyBackendG_congrDel`**, (2) the bridge's docstring, (3) `kbMW`'s
docstring, (4) the `srSlot` margin notes. The user has nothing to decide (see "For the user").

---

## 1. `ContractLaws.lean`

**Good.**
- The monotonicity laws are stated where `Del` actually occurs. In `keyReadSnap`/`snapThin` and in
  `batchTxSpecG`'s single-key `UnsafeRange` it occurs covariantly (InvStore.lean:652-654, 790, 1197).
  In the `⌜Cmp⌝` range's post it is covariant again (`snapThin m m' Del`, 1217), and only the
  delete's pre (1222) is contravariant. `SR`/`SRh` (1407-1410) and `MW` (the two `⌜Cmp⌝` clauses of
  `batchTxSpecG`) occur only under `⌜Cmp⌝`. So `isKeyBackendG_weaken`, which takes any `Cmp'` that
  does not hold and any `SR'`/`SRh'`/`MW'`, is correctly stated (F7) and proved.
- `isKeyBackendG_weaken_noDel` matches the Draft's `isKeyBackendG_weaken.stmt` (WiringDraft.lean:265)
  and is more general (any `Cmp`, not only `True`).
- The proofs eliminate `◇` in covariant posts through `wp_fupd`, which is sound and keeps the
  statements free of `◇`.

**F1 (tier 1: sufficient for its caller). `isKeyBackendG_congrDel`'s premise
`□ (∀ k, Del k ∗-∗ ◇ Del' k)` cannot be established for the instance the core stage needs.**

- *Evidence.* The plan (notes/backend-cmp-plan.md:1341-1345) says a compacting store registers
  `storeDlReg γB γi`. That is `dlReg γB (fun nk => ⌜nk.1 = keyName⌝ ∗ delKeyI γi nk.2)`
  (WiringDraft.lean:256-258). The store's `Del'` is then `delKey γ` (= `delKeyI γ.idx`; the store's
  contract uses `delKey γ`, InvStore.lean:2349, 2836), and the law is meant to carry the bridge's
  `Del := bkDel γB` (= `dlIs γB (key, k)` = `∃ Φ, dlReg γB Φ ∗ □ Φ (key,k)`, InvBackend.lean:554;
  BackendBridge.lean:2512) over to it.
  - The forward direction holds: `bkDel k ⊢ ◇ delKey k` (saved-predicate agreement gives
    `▷ (⌜…⌝ ∗ delKeyI k)`, and `delKey` is timeless, InvStore.lean:1942).
  - The backward direction `◇ delKey k ⊢ bkDel γB k` is not derivable. Its goal, an existential
    over a saved predicate's ownership and `□ Φ nk`, is not except-0 closed (no `IsExcept0`
    instance for `own`/`savedPredOwn`), so the `◇` cannot be eliminated. Registering `◇ delKeyI` or
    `▷ delKeyI` instead breaks the forward direction (`▷ ◇ X` and `▷ ▷ X` do not give `◇ X`).
  - No `Del'` the store would use satisfies both directions.
- *What the proof uses.* Only `Del k -∗ ◇ Del' k` (`Hf`) and `Del' k -∗ Del k` (`Hb`). The latter is
  derived from the `∗-∗` by `imodintro` (ContractLaws.lean, `batchTxSpecG_congrDel`, the
  `ihave #Hb` step). `Del' k -∗ Del k` is easy for the instance: take `Φ := storeDlReg`'s predicate
  and use that `delKey` is persistent.
- *Caller affected.* The core stage's switch (`storeBackend_of_backend` over the new bridge at
  `cm := true`, plan:1343-1345, 1651-1659). As stated, the law cannot be applied there.
- *Restatement* (strictly stronger, same proof):
  ```
  isKeyBackendG … Del … Cmp … ∗ □ (∀ k, Del k -∗ ◇ Del' k) ∗ □ (⌜Cmp⌝ -∗ ∀ k, Del' k -∗ Del k) ⊢
    isKeyBackendG … Del' … Cmp …
  ```
  The `⌜Cmp⌝` guard is optional: the backward direction is used only in the `⌜Cmp⌝` range's delete
  clause. Apply the same change to `batchTxSpecG_congrDel` and `isBatchTxG_congrDel`, and update
  `WiringDraft`'s `isKeyBackendG_congrDel.stmt` and the plan's line 1695.
- This statement is the Draft's, so earlier rounds missed it too. The glue against the real
  instance would have caught it, which supports writing that glue (`storeDlReg` →
  `□ (∀ k, bkDel k -∗ ◇ delKey k)` and `□ (∀ k, delKey k -∗ bkDel k)`) before the core stage
  builds on the law.

**P1 (preference: one law).** R4-4 recorded a single law
(plan:633-637: `□ (∀ k, Del k -∗ Del' k) ∗ □ (⌜Cmp'⌝ -∗ ∀ k, Del' k -∗ Del k)`, `Cmp' → Cmp`). The
module has two, `weaken` (only `Cmp'` false) and `congrDel` (same `Cmp`). With F1's restatement the
two merge into one:

```
□ (∀ k, Del k -∗ ◇ Del' k) ∗ □ (⌜Cmp'⌝ -∗ ∀ k, Del' k -∗ Del k)
```

for `Cmp' → Cmp`, with `SR`/`SRh`/`MW` arbitrary when `¬Cmp'`. The current layout's `weaken_noDel` is
then that law's instance. This is not required. Two laws are acceptable, since both are proved and
neither is a spec family.

## 2. `BackendBridge.lean`: the Cmp-parametrized bridge

**Good.**
- **One bridge, not a hidden family.** The mode is a parameter (`Cmp : Prop`, to be `d.cm = true`
  at the switch, plan:1427). The old bridge `isKeyBackendG_of_backend` is now a corollary of the one
  proof: `_of_backendC` at `Cmp := False`, then `isKeyBackendG_weaken_noDel` under `dlNoDel`
  (BackendBridge.lean:3263-3273 at 7deaf43ae3). The skill allows exactly this ("a variant a client
  finds handier is fine only as a corollary of the one proof"). The old bridge's separate ~110-line
  proof is gone, so the duplicate read proofs R4-4 targeted are gone too.
- **Nothing finished got weaker.**
  - `isKeyBackendG_of_backend`'s statement is unchanged character for character (the diff touches
    only its docstring and proof). Its exports (`mvcc_backend_bridge`, Results.lean:216-235, and
    `storeBackend_of_backend`, BackendBridge.lean:3339) are untouched.
  - `_of_backendC` at `Cmp := True` is equivalent to its former statement: `True → X` is `X`, and
    `□ (⌜True⌝ -∗ fkV γ true)` follows from the persistent `fkV γ true` (InvBackend.lean:355-358).
  - The trust base is unchanged (the log's tcb check). The old bridge reaches no `sorry` through
    `bt_rangeC`/`bt_metaPut`/`rt_metaWf`: BackendBridge.lean has none.
- **The guarded premises are right.**
  - `hLSR`, `hUSR` and `hUP` are used only inside the `⌜Cmp⌝` clauses (`iintro !> %hc` before each
    use).
  - `hHK` and `hFV` are likewise used only in `bt_rangeC`, `bt_metaPut` and `rt_metaWf`, all under
    `hc`.
  - `fkV γ true` is needed only by `rt_metaWf` (the `⌜Cmp⌝` `ReadTx`). It is now
    `□ (⌜Cmp⌝ -∗ fkV γ true)`, persistent, so the premise is no stronger than the code requires
    (no unneeded premise).
  - `keySized` stays unguarded and is used by the non-compaction `ReadTx` range.

**D1 (docs).** `_of_backendC`'s docstring (BackendBridge.lean:3033-3043) still says "with `Cmp` true",
"the bit `fkV γ true`" and "the stores switch to it at the wiring step". It should now say `Cmp` is a
parameter, that its compaction-only premises (`hLSR`/`hUSR`/`hUP`/`hHK`/`hFV`, `fkV`) are guarded by
`Cmp`, and that the old bridge is its `Cmp := False` instance. Related stale comments:
`InvStore.lean`'s `kbCmp` docstring (1676-1681: "until then the stores keep the old one") and
`InvCompact.lean:184`. These are tolerable until the switch, but `_of_backendC`'s is now false.

**P2 (preference).** The corollary still fixes `MW := ∃ f, fkOwn γ f` and the default `SR`/`SRh`,
although `weaken_noDel` allows any. Keeping the exports unchanged is a reasonable choice (fewer
diffs to D22's walk and `NewServer`). Generalizing them later is a pure strengthening, so there is
nothing to do now.

## 3. `InvStore.lean`: `viewFk`, `viewNoCmp := viewFk γb 0`

**Good.**
- `viewNoCmp`'s users mean the same thing. Before, `viewNoCmp γb` was an opaque atom with no laws.
  Now it unfolds to `viewFk γb 0`, which is again an opaque atom with no laws, so every proof that
  used `viewNoCmp` abstractly is unaffected. No statement's text changed (`kbNoCmp none` and
  `NewStore`'s/`New`'s premises), and the build passed.
- `viewFk` is an `opaque` with no axiom, so it adds nothing to the trust base.
- Deferring `kbMW none := ∃ f, viewFk γb f` to the core stage is justified in the plan
  (plan:1712-1720: `store__scheduleCompaction` and `SetScheduledCompact`/`SetFinishedCompact`
  produce `kbMW none` trivially today).

**D2 (docs).** `kbMW`'s docstring (InvStore.lean:497-507 at 7deaf43ae3) still describes `viewFk` as a
hypothetical ("an opaque `viewFk` mirroring the real backend, `viewNoCmp γb := viewFk γb 0`, would
make…"). It should say that `viewFk` exists, that `kbMW none` is still `True` until the core stage,
and that, therefore, as before, an honest assumed backend cannot maintain `viewFk γb 0`: a `Meta`
put needs no right. Results over `kbNoCmp none` stay vacuous, not wrong. This is unchanged by these
commits, but the docstring should say so in present terms.

## 4. `srSlot` in `newPost`/`newPostK`; `newBackend`; `storage.OpenBackend`

**Good.**
- **True of the Go code.**
  - `newBackend`'s composite literal (`/shared/etcd-grove/.lake/go-src/etcd/server/storage/backend/backend.go:240-270`)
    leaves `safeRangeDeleteMu` (field at :140) at its zero value. The proof (`newBackend.lean:196-201`)
    makes Perennial's `init_RWMutex` slots from that zero value (RWMutexGuard.lean:527) at predicate
    `True` and takes one (`rep_one`).
  - The field is used only by `LockForSafeRangeDelete`/`UnlockForSafeRangeDelete` (`RLock`/`RUnlock`,
    backend.go:1115-1121) and `defragNonBlocking`'s `Lock` (:699-700). Nothing between construction
    and the return touches it, so `OpenBackend`'s axiom gains a claim that `newBackend`'s proved spec
    already carries.
- **Exclusive / duplicated.** `srSlot b` is one reader's slot (`ownRWMutex`, which holds one
  `ownRLockToken`, RWMutexGuard.lean:124-133). Its only producer is `newPost`/`newPostK`
  (`git grep srSlot`: DelKeys.lean:130, InvNew.lean:71/168, NewAlloc.lean:457, newBackend.lean:200).
  Its consumers are the bridge (`SR`) and `kbSR (some d)` (InvStore.lean:1538-1541). No caller
  already holds one, so there is no duplication. Read slots are shared in Go anyway, so even a
  duplicate would not be unsound. One slot is enough because compaction jobs run one at a time.
- **Callers.** `bootBackend_of_newPost` (BootBackend.lean:91) and `applySnapshot_walk`
  (SnapApplyWalk.lean:285) drop the slot with `-`, which is sound (affine) and correct while
  `cm := false`. 7deaf43ae3's fix is just the extra pattern element.

**M1 (margin, record only).** `newBackend` discards the other `actualMaxReaders - 1` slots and does
not keep `safeRangeDeleteMu`'s guard (`rep_guard`, used for `b.mu` at newBackend.lean:192, is not
applied to this mutex). A future proof of `Defrag` (the mutex's only writer, `Lock` at backend.go:699)
will need either the persistent `isRWMutexGuard` in `isBackend` or a slot. That is a change to
`newBackend`'s proof and to `isBackend`'s body, not to any spec's text, so it costs nothing now. A
line in `kbSR`'s docstring or the plan would keep it from being rediscovered.

**M2 (process).** The post of `storage.OpenBackend` (a trust-boundary axiom) now means more. The plan
already lists the `axiom` skill run on it before the freeze (plan:1681, 1689-1693). This is noted
correctly; it is still owed.

**Threading at `cm := true` (not a finding).** At the close step, `bootBackend_of_newPost` must pass
`srSlot` on instead of dropping it, into `compactJobRes`'s `kbSR`. The plan's close step covers this
implicitly.

## For the user

Nothing needs a decision.
- The agent's two choices are consistent with the plan and the skill:
  - The old bridge as the `Cmp := False` instance with its exports kept. This is the plan's (iv),
    plan:1346-1349, with the exports unchanged.
  - Moving `kbMW`'s switch into the core stage.
- F1 is a restatement with no design choice: the law's premise becomes the two one-way implications
  its proof already uses.
- F1 is the third round touching the `congrDel` statement (the Draft's F7 in round 1, R4-4 in
  round 4, now). By the stopping rule, verify the fix with the glue against `storeDlReg`, not with
  another review round.
