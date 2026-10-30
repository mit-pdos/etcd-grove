# backend-cmp, Review round 16 (2026-10-29): question 5's Draft (the wiring), third round

**Under review.** `0ed5b49b3f` (`HEAD`): the Draft repaired after round 15 (N1-N5, the user's Q5-4 (a),
two glue proofs: `mwSwap_of_inv`, `restore_noCmp`); diff against `a748d15356`. No finding of round 15
is open at `HEAD`, and no finding below is stale. As in round 15, every statement is judged as it
will be switched in: `cm` is `KBReal.cm`, `kbCmpM kb cm` is `kbCmp kb`, and `γmk` is `γ.mk`.

**Stop rule.** This is the increment's **third** round. **No first-tier finding is left** in the
drafted statements. None of the findings below comes from a defect in round 15's repaired
statements. One finding (M1) is churn in the *list*, not in the statements: Q5-4 (a), which round 15
recommended, reaches more D22 statements than round 15 listed. Next step: write the switch and its glue
against the real callers. Do not run a fourth round. The only item for the user is to confirm Q5-4 (a)
at its real cost (M1).

**Read.**
- `WiringDraft.lean` (whole), the plan's question-5 sections (`notes/backend-cmp-plan.md:1294-1626`),
  and `backend-review-15.md`.
- `InvStore.lean`:
  - `KBReal`/`StoreNames`/`PhysNames`/`withPhys` (`:81`, `:116`, `:235-262`), `kbMW` (`:499`);
  - `kbRT`/`kbSR`/`kbWTSupply`/`compactJobRes` (`:1512-1558`), `kbCmp` (`:1672`), `batchTxSpecG`
    (`:1155-1245`);
  - `compactTok`/`compactQueue`/`compactRight` (`:1822-1870`);
  - `writerRes` (`:2141`), `lateW`/`storeW`/`storeRegd` (`:2181-2205`), `storeW_get`/`_put`/`_register`
    (`:2218-2275`), `writerReg`/`writerInvBody` (`:2279-2310`);
  - `physOk`/`fieldShareAt` (`:2822-2846`), `poolBody`/`retiredAt`/`readerPool` (`:3020-3039`),
    `storeStop` (`:5030`), `storeCloser`/`compactRight_of_closer` (`:5097-5115`).
- Proofs and specs:
  - `NewStore.lean` (where `storeW_register` (`:353`), `restore` (`:424`), the pool (`:456`) and
    `physOk` (`:513`) are);
  - `RestoreMoves.lean` (`restore_switch` `:301-322`);
  - `Spec/…/mvcc/store__Restore.lean` and `watchableStore__Restore.lean`;
  - `etcdserver`: `Results.lean` (`server_kv_backend` `:812`), `BuildLemmas.lean` (`:35-90`),
    `NewServer.lean` (`:566-590`), `InvBoot.lean` (`bootOk` `:247-400`), `InvApplier.lean` (`:478`,
    `:554`, `:830`), `SnapApplyWalk.lean` (`:53`, `:283-290`, `:395-401`), `SnapApplyDefs.lean`
    (`:64-70`, `:90-111`), `Spec/…/etcdserver/EtcdServer__applySnapshot.lean` (`:54-60`).
- Perennial's docs on later credits (`PERENNIAL_PROOF_REFERENCE.md:219-246`, `:965-975`).
- Go at the pin:
  - `mvcc/kvstore.go`: `NewStore` `:87-134`, `updateCompactRev` `:197-222`, `Compact` `:263-277`,
    `Restore` `:290-314`, `restore`'s resumption `:411-412`;
  - `mvcc/kvstore_compaction.go:28-105`, `mvcc/store.go:38-60`;
  - `grep` over `server/`: the compaction keys are written only by `SetScheduledCompact` (via
    `updateCompactRev`) and the job's `UnsafeSetFinishedCompact`.
- No build. I did not re-run `etc/lean-check.py` on the two glue proofs. Their correctness rests on
  the author's check (the plan: `lean-check -a` and a targeted `lake build --packages`). Neither has a
  `sorry`.
- No Go bug found; no `issues/` entry.

## Summary

| # | tier | target | finding |
|---|---|---|---|
| M1 | second (completeness; D22; for the user) | Q5-4 (a)'s list | `cm = false` must also reach `watchableStore.Restore.spec`, `applySnapshot.specSnap` (with the walk's lemmas) and the snapshot post. At boot `d` is an existential (`bootOk`), not a literal. One `InvApplier` fact suffices, not three |
| M2 | second (completeness) | N4 | `server_kv_watchable_of` (`BuildLemmas`) needs `hcm` too, and `NewServer`'s proof must build `d` with `cm := false`, since `bootOk` quantifies `d` |
| M3 | second (completeness) | internal statements and proof sites | `restore_switch`/`restore_finish` need the two `cm = false` facts; `storeTxnWrite.End` rebuilds `writerRes`; `KBReal`'s `Countable`; D22's record literals |
| M4 | second (text) | Draft | the header (ii) still describes round 14's disjunctive invariant. `mwSwap_of_physOk.stmt` takes `γmk` apart from `writerRes`'s key. The "one law" count is stale |

## N1's repair: the key, `mwInvW`, `mwSwapW` with `£ 1`

**Good.**
- **The swap law is sound, and it is proved** (`mwSwap_of_inv`, `WiringDraft.lean:173-210`).
  - The toggled ghost removes the need for an exclusive right. Acquire: the halves agree on `true`;
    the right comes out; both halves become `false`. Return: they agree on `false`; the right goes in;
    both become `true`.
  - A third party that holds some other `fkOwn` half can no longer steal the key: the key's other half
    is a `ghostVar` half, and only the lock's resource holds it.
  - The return direction needs no credit: `ghostVar` is timeless (`>Hh`), and the old contents
    (`▷ True`) are dropped.
- **The credit is usable.** The credit is in the antecedent of the `□` wand, so the session that
  swaps spends it, not the caller.
  - `updateCompactRev`, `SetScheduledCompact`'s only caller, passes the persistent
    `mwSwapW (storeW s γ) (kbMWW …)` from `physOk` and needs no credit.
  - `SetScheduledCompact`'s proof takes `£ 1` from a pure step before `LockInsideApply`
    (`wp_auto_lc 1`, `PERENNIAL_PROOF_REFERENCE.md:226`). Go's body has them: the defer setup and the
    call (`store.go:38-42`).
  - The job swaps in its last batch (`kvstore_compaction.go:68-71`). Every loop iteration takes pure
    steps (`var rev`, `start := …`), so a credit is available. It does not compete with the receipts:
    every Go step gives both `⧗ 1` and `£ 1` (`:972`).
  - `SetFinishedCompact` has no caller.
- **The credit is the margin of the assumed backend only.** For `some d`, `kbMWW` is
  `∃ f, fkOwn d.γB f`, which is timeless. `£ 1` is needed only because `viewFkW` is opaque. That is
  fine: making `viewFkW` timeless would take an axiom. The docstring (`:124-126`) already says so.
- **Who writes the compaction keys.** Only the two sessions above, each holding the batch lock for
  the whole write (`grep` over `server/`). Between `NewStore`'s first `Unlock` (`NewStore.lean:353`)
  and the invariant's allocation (after `:424`, before `physOk` at `:513`), nothing swaps: `restore`
  resumes no compaction under `kbNoCmp` (`kvstore.go:411`).

**No finding.**

## N3's repair: `physCmpW` in `physOk`, and `storeRegd`

**Good.**
- **The placement works.**
  - `physOk` is per physical names.
  - It is persistent: `mwInvW` is an `inv`, `storeRegd` has `storeRegd_persistent` (`:2207`), and
    `kbWTSupply` is `True` or `□ …`.
  - It reaches both users through `□ physOk`: `store.Compact` and the job through `storeStop`
    (`:5030`), the writers through `fieldShareAt`.
  - `isStore` and `isStore_withPhys` (`rfl`) are untouched.
- **`NewStore` has everything at the right point.**
  - `Hregd` comes from `storeW_register` at `:353`.
  - `restore` returns the right at `:424`.
  - `physOk` is built at `:513`, after both, so `physCmpW` can be proved there.
- **`mwSwap_of_physOk.stmt` is provable as written, once `writerRes` has `mwSlotW` at `γ.mk`.**
  1. `storeW_get` (a plain entailment: no `▷`, no credit) needs `storeRegd`, which `physCmpW` now has.
  2. Split `writerRes` into `mwKeyW γ.mk ∗ R`; `R` is the rest, under its `∃ L`.
  3. Apply `mwSwap_of_inv`.
  4. On return, `storeW_put`.

  About 20 lines.
- **"A compacting store is never restored" is now enforced.**
  - Before round 15 it was argued; now it is `store.Restore.spec`'s Q5-4 premise.
  - `compactRight_of_closer` also excludes restore for the store the job runs on.
  - So `storeRegd`, persistent, stays true for every names `physCmpW` is non-trivial at.
- For `kb = none`: `storeRegd` and `kbWTSupply` are `True`, and `mwInvW` is allocated as for the real
  backend.

**M4 (second tier, text).** `mwSwap_of_physOk.stmt` (`:141-143`) quantifies `γmk` independently of
the key that `writerRes` holds (`γ.mk` at the switch). As written, it is true only when
`γmk = γ.mk`. State it at `γ.mk`, or with `γmk` replaced, as `physCmpW` will be.

## N2 / Q5-4 (a): `store.Restore`'s premises

**Good.**
- **`restore_noCmp` (`:222-236`) is the right glue.** Under the premise:
  - `nJobRd = 0` and `poolSumW = nReaders`. So `restore_switch`'s count (`k = nReaders - 2`, `r = 2`)
    and the post's `nReaders - 1` keep their text.
  - `compactJobResM`, `mwSlotW` and `physCmpW` are `⊣⊢ True`. They are then discharged for the new
    names `γ.withPhys p'`, since `(γ.withPhys p').kb = p'.kb = some d'`.
- **The old-store premise is the store's current backend.** `γ` in `store.Restore.spec` is the
  current names (`storeCloser s γ`, `writerFrag γ`), and the post hands back `γ.withPhys p'` for the
  next restore. So `γ.kb` is the backend being replaced, as N2 needs.
- **It is a filed scope restriction** (hard rule "No unneeded premise"). Go restores a compacting
  store without trouble; the premise is M2's "no restore in compaction mode" (`m2-plan.md:252` on
  branch `m2`). At the switch, `store.Restore.spec`'s docstring should say so and point there.

**M1 (second tier, completeness of the D22 list; for the user).** The premise must reach the code
that calls `Restore`. The plan's D22 list (`backend-cmp-plan.md:1614-1616`) has only
`store.Restore.spec` and `InvApplier`'s three facts. The call chain is:
- `EtcdServer.applySnapshot.specSnap` takes `(hkb : E.γ.kb = some d)` as a named premise
  (`Spec/…/EtcdServer__applySnapshot.lean:59-60`; S-j1 discharges it, and it has no caller yet).
- It passes `hkb` to `applySnapshot_walk` (`SnapApplyWalk.lean:53`) and `srvSnapApplied_of_walk`
  (`EtcdServer__applySnapshot.lean:116-125`).
- The walk calls `watchableStore.Restore.spec` (`SnapApplyWalk.lean:395-401`, `⟨d, by … hkb⟩`). That
  spec has its own `⌜∃ d, γ.st.kb = some d⌝` (`Spec/…/watchableStore__Restore.lean:47`).
- `watchableStore.Restore` calls `store.Restore` (`watchableStore__Restore.lean:225`).

So these statements change too:
- **`watchableStore.Restore.spec`**: both premises, the old record's `cm = false` (Q5-4) and the new
  record's (Q5-3). Round 15 missed the Q5-3 premise here as well.
- **`applySnapshot.specSnap`**: `(hcm : d.cm = false)` beside `hkb`. `applySnapshot_walk` and
  `srvSnapApplied_of_walk` take the same hypothesis (lemma statements).
- **The snapshot's post**: whatever re-establishes the `InvApplier` fact for the new environment
  (`SnapApplyDefs.lean:90-111`, `∃ d' … p'.kb = some d'`) must carry `d'.cm = false`.
  - The walk's `d'` is `{ d with γB, be, gx }` (`SnapApplyWalk.lean:288`), which inherits `d.cm`. So
    it is `false` by `hcm`, or by writing `cm := false` there.
- **At boot there is no literal record.** `bootOk` quantifies `d` (`InvBoot.lean:253`) and uses it
  only through `d.γB`, `d.P`, `d.be`, `d.gx`. So `NewServer`'s proof builds `{ d with cm := false }` (as
  `SnapApplyWalk:288` does) and uses it everywhere. `bootOk` and `NewServer.spec` keep their text. The
  plan's "they hold at boot (the literal record)" (`:1564`; round 15 `:208`) should say this. `NewServer.lean` goes
  back into the proof sites (round 14's list dropped it, `:1541`).
- **Minimality.** One `InvApplier` fact is enough: `srvEnvOk`'s (`:478`), whose shape `specSnap`'s
  `hRO` already mirrors. `srvBeOwn` (`:554`) and `srvWTStock` (`:830`) quantify the same `d`, since
  `E.γ.kb` determines it. Adding the conjunct to all three is redundant.

**For the user.** The choice between (a) and (b) is still the user's. Round 15 presented (a) as "a
few lines", and that undercounted it:
- (a) changes the text of about five D22 statements: `store.Restore.spec`, `watchableStore.Restore.spec`,
  `specSnap` (with two walk lemmas), `srvEnvOk` and the snapshot post's record fact. Each change is a
  pure conjunct or hypothesis, about +40 lines over round 15's +50.
- Under (b), the old store's mode is never needed. The only D22 text change is Q5-3's `d'.cm = false`,
  in `store.Restore.spec` and `watchableStore.Restore.spec`. The walk discharges it by building `d'`
  with `cm := false`. In exchange, (b) changes `storeCloser`, `compactRight_of_closer`'s proof and
  `Restore`'s proof (about +120).

I would keep (a): it states M2's restriction where it applies, and the extra conjuncts are pure. But
the user should confirm it at this cost. This is no reason for another round.

## N4: `server_kv_*` gain `hcm`

**Good.**
- `server_kv_backend`, `server_kv_watchable` and `server_kv_backend_hooks` are generic in `d`.
- With `hcm`, `nJobRd (some d) = 0`, so their posts' `actualMaxReaders` (`Results.lean:849-850`)
  hold.
- These are exported results: no proof calls them.

**M2 (second tier).**
- `server_kv_watchable_of` (`BuildLemmas.lean:35-90`) is the lemma `NewServer` actually calls
  (`NewServer.lean:580`). It is generic in `d`, and its post gives `actualMaxReaders - 2` watch
  readers. So it needs `hcm` as well.
- Its caller does not "build `d` with a literal `cm := false`" (plan `:1593`; round 15 `:290`): `d` comes from
  `bootOk`'s `∃`. The fix is M1's: `NewServer`'s proof uses `{ d with cm := false }`.
- With that, `NewServer.spec` is indeed unchanged.

## N5: `poolSumW` in `poolBody`

**Good.**
- `poolSumW kb cm = nReaders - nJobRd kb cm` (`:215`), at `poolBody (γ.withPhys p)` with `p.kb`.
- `NewStore` allocates the pool with `k = nReaders - nJobRd`, `j = w = r = 0`. That matches its post's
  `actualMaxReaders - nJobRd kb cm` tickets and `retiredAt γ 0`.
- `readerPool_checkout`/`_retire` keep the sum, so their statements are untouched.
- The spare `idxReader` of a compacting store is dropped.
- No statement text changes, as the plan says.

**M3 (second tier, internal statements).**
- `restore_switch` (`RestoreMoves.lean:301`) and `restore_finish` (`:486`) are generic in `p'`, and
  `restore_switch` opens the old pool.
  - They need `∃ d, γ.kb = some d ∧ d.cm = false` and `∃ d', p'.kb = some d' ∧ d'.cm = false` as
    hypotheses: for `poolSumW` of the old and the new names, and for `mwSlotW (γ.withPhys p')` in the
    pending `writerRes`.
  - These are internal lemmas of mvcc, not D22's client statements, but their text changes. The plan
    (round 15 `:227`) says "`RestoreMoves` is otherwise untouched"; it is not.

## F5's `□`

Dropped (`:336`). `kbWTSupplyM kb cm` is persistent by its definition, so the new pre is equivalent
to the old one, and smaller. `physCmpW` uses `kbWTSupply γ.kb` under the same gate. No finding.

## The rest of the Draft

- `NewStore.specW`, `store.Compact.specW`, `SetScheduledCompact.specW`, `compactTokW`,
  `compactJobResM`, `kbSRM`, `nJobRd`, `isKeyBackendG_weaken.stmt`, `isKeyBackendG_congrDel.stmt`:
  their text is unchanged since round 15, and round 15's checks still hold. No finding.
- **M4 (text).**
  - The header's (ii) (`:13-18`) still says `NewStore` "allocates an invariant holding the right or a
    lock key", which is round 14's unsound design. Say "the other half of the key's ghost variable,
    with the right when it is `true`" (as `:113-116` does).
  - `:7` says "the one law here is proved"; three are now proved (`kbNoCmpW_MW`, `mwSwap_of_inv`,
    `restore_noCmp`).

## The listed changes: complete? minimal?

- **Client-visible (mvcc).** Round 15's list plus `store.Restore.spec`'s two premises is right. It
  misses `watchableStore.Restore.spec`, which takes the same two premises (M1). `NewStore.specW` without
  `□`: right.
- **Exported results.** As listed. `server_kv_*`'s `hcm` is right. Add `server_kv_watchable_of`'s
  `hcm` (a `BuildLemmas` statement; M2).
- **Trusted.** Complete: only `storage.OpenBackend` changes, in meaning (Q5-2). `OpenSnapshotBackend`
  is proved from it (`Proof/…/storage/OpenSnapshotBackend.lean:44`), so it needs no axiom check of
  its own.
- **D22's.**
  - Statement text: add `watchableStore.Restore.spec`, `applySnapshot.specSnap` (and its walk lemmas)
    and the snapshot post's `d'.cm = false`. Drop two of the three `InvApplier` conjuncts (M1).
  - Definitions and proofs:
    - `SnapApplyDefs`' literal records `kbP_mk`/`kbgx_mk` (`:64-70`) need `cm`;
    - `SnapApplyWalk:288` inherits it;
    - `NewServer.lean`'s proof builds `{ d with cm := false }`;
    - `restore_switch`/`restore_finish` hypotheses (M3).
  - A field default `cm : Bool := false` would keep the literals' text unchanged but hide the mode.
    Prefer writing it out.
- **Proof sites that round 14's list lacks.**
  - `KBReal`'s `Countable` instance (`InvStore.lean:219`), beside the two that the plan names;
  - `storeTxnWrite__End.lean`, which rebuilds `writerRes`, so `mwSlotW` threads through;
  - the `physOk` destructurings (`store__Write`, `store__Commit`, `store__Close`, `store__compact`,
    `store__compactBarrier`, `watchableStore__syncWatchers`), harmless if they use `iNamed`;
  - `NewServer.lean` and `BuildLemmas.lean` (M1, M2).
- **Still the user's.** Only the confirmation of Q5-4 (a) at its real footprint (M1). Everything
  else is the agent's.

## Estimate

Round 15's 1250-1600 lines, plus about 40 for M1 (the hypothesis threaded through `specSnap` and the
walk, `watchableStore.Restore`, `NewServer`'s record) and about 15 for M3. That is about
**1300-1650**.

## Ranking (two-tier rubric)

No target has a first-tier finding.

1. **Q5-4 (a)'s reach into D22** (`store.Restore.spec`, `watchableStore.Restore.spec`, `specSnap`,
   `InvApplier`): M1, second tier. The list is incomplete and over-broad, and its cost was understated
   to the user.
2. **`server_kv_*` / `server_kv_watchable_of`**: M2, second tier.
3. **`poolSumW` / `RestoreMoves`**: M3, second tier.
4. **`mwSwap_of_physOk.stmt`, the Draft's header**: M4, text.
5. **`mwKeyW`/`mwInvW`/`mwSwapW`/`mwSwap_of_inv`, `physCmpW`, `NewStore.specW`,
   `SetScheduledCompact.specW`, `store.Compact.specW`, `restore_noCmp`, the rest**: no finding.

**Verdict.** Round 15's repair converged: N1 is proved sound, N3's home works, N2's glue is proved,
and N4/N5 are right. No first-tier finding remains in the third round, and none comes from round 15's
repair. Under the stop rule, go to the switch. Write its glue against the real callers
(`updateCompactRev`, the job's last batch, `NewStore`, `store.Restore` through `watchableStore.Restore`
and `applySnapshot_walk`, `NewServer` through `server_kv_watchable_of`), with M1-M4 folded in. The
glue will find what this review could not.
