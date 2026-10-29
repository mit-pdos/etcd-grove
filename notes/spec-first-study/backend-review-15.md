# backend-cmp, Review round 15 (2026-10-29): question 5's Draft (the wiring), second round

**Under review.**
- `391dff074f`: the Draft repaired after round 14 (`WiringDraft.lean`; the plan's "Question 5's
  Draft, repaired after review round 14").
- `a748d15356` (`HEAD`): the user's answer to Q5-3, (a), notes only.

No finding is stale at `HEAD`. I judged every statement as it will be switched in: `cm` is
`KBReal.cm`, and `kbCmpM kb cm` is `kbCmp kb`.

**Stop rule.** This is the **second** round of the increment. Two first-tier findings come from round
14's repair, which is the sign of churn the rule names:
- **N1**: the swap's invariant is unsound. Its design is my round-14 option (a), copied exactly.
- **N2**: Restore cannot return the job's reader. My round-14 note said it could, and that note was
  wrong.

Neither undoes an earlier decision, and each has a local fix (below). So: repair, then run round 16 on
the same statements. Before round 16, write two glue proofs: the swap law (`mwSwap_of_inv`) and
`store.Restore`'s reader count. Round 16 would be the third round. If it still finds a first-tier
problem in the write right's home or in the reader accounting, stop reviewing those statements and
write the switch's proofs against the real callers.

**Read.**
- The Draft (whole) and the plan's question-5 sections (`notes/backend-cmp-plan.md:1294-1555`).
- `InvStore.lean`:
  - `KBReal` (`:81`), `StoreNames`/`PhysNames`/`withPhys` (`:116`, `:235-262`), `kbMW` (`:499`);
  - `batchTxSpecG` (`:1155-1245`), `kbRT`/`kbSR`/`kbWTSupply`/`compactJobRes` (`:1512-1558`);
  - `compactTok`/`compactQueue`/`compactRight` (`:1822-1870`), `crevFrozen` (`:1881`);
  - `compactRes` (`:2094`), `writerRes` (`:2141`), `lateW`/`storeW`/`storeRegd` (`:2181-2210`);
  - `storeW_get`/`storeW_put`/`storeW_register` (`:2216-2262`), `writerReg` (`:2279`);
  - `physOk` (`:2822`), `nReaders` (`:2967`), `poolBody`/`retiredAt`/`readerPool` (`:3020-3039`);
  - `isStore`/`isStore_withPhys` (`:3347-3376`), `storeBackend`/`storeBackendT` (`:3427-3446`),
    `storeCloser`/`compactRight_of_closer` (`:5097-5115`).
- `InvBackend.lean:345` (`fkOwn`), `DelKeys.lean:130` (`srSlot`).
- Specs: `store__Restore`, `NewStore`, `New`, `newWatchableStore`, `SetScheduledCompact`,
  `store__Close`, `schedule/Scheduler__Stop`.
- Proofs:
  - `store__Restore.lean` (`:80-130`, `:140-230`, `:340-390`);
  - `NewStore.lean` (`:201-213`, `:320-345`, `:440-470`);
  - `store__updateCompactRev.lean` (`:230-300`);
  - `etcdserver/Results.lean` (`server_kv_backend`, `:807-870`).
- Go at the pin (`/shared/etcd-grove/.lake/go-src/etcd/server/storage/mvcc/`):
  - `kvstore.go`: `NewStore` `:87-134`, `updateCompactRev` `:197-222`,
    `checkPrevCompactionCompleted`/`compact`/`compactLockfree`/`Compact` `:225-282`, `Restore`
    `:290-314`, `restore` `:317-`;
  - `store.go:38-60`;
  - `kvstore_compaction.go:28-105`.

**Checked.**
- `etc/importers.py --count InvStore.lean`: 1724 modules, 300035 lines.
- `--uses` for `PhysNames`, `poolBody`, `storeCloser`, `nReaders`, `retiredAt`, `physOk`,
  `writerRes`, `isStore_withPhys`.
- No build. No Go bug found; no `issues/` entry needed.

## Summary

| # | tier | target | finding |
|---|---|---|---|
| N1 | first (truth) | `mwInvW`/`mwSwap_of_inv.stmt` (F1's repair) | the swap law is false: the right can come back to an invariant that holds the right, and the key is then lost |
| N2 | first (sufficiency; D22) | `store.Restore.spec` under F2 | an old store in compaction mode has given one reader to its job, which `Restore` cannot get back, so its post's `nReaders - 1` cannot be proved. Q5-3 constrains only the new record |
| N3 | first (placement) | `mwInvW` "in `isStore`" | `mwInvW` names physical names, so putting it in `isStore` breaks `isStore_withPhys` (`rfl`, D22's). The swap from `storeW` also needs `storeRegd` |
| N4 | second (completeness) | `server_kv_*` | the claim "reader counts unchanged (`cm := false`)" needs a premise `d.cm = false`, or the counts written with `nJobRd` |
| N5 | second (completeness; D22) | the list of D22 changes | `PhysNames`/`StoreNames` gain `mk`; the pool's count (`poolBody`, or `retiredAt` in `NewStore`'s post) must account for the job's reader |

Round 14's repairs that hold: F2 (`nJobRd`), F3 (`compactJobResM`), F4 (`γ.idx = γi`), F5
(`□ kbWTSupplyM` in `physOk`), F6 (`SetScheduledCompact.specW`), F7 (`isKeyBackendG_weaken.stmt`).

## F1's repair: the write right's home

**Good.**
- **The key is exclusive.** `mwKeyW γmk = ghostVar γmk 1 ()` (`WiringDraft.lean:102`).
- **The key is deposited at the right point in Go's order.** `writerRes` is deposited at the first
  `tx.Unlock()` (`kvstore.go:124`; `NewStore.lean:335-345`). That is before `s.restore()` (`:129`).
  The invariant is allocated after `restore` returns the half.
- **Nothing needs the swap before the invariant exists.** Between the deposit and the allocation, only
  `NewStore` runs. `restore` resumes no compaction: `kbNoCmp` means `UnsafeReadScheduledCompact` finds
  nothing, so `scheduledCompact = 0` and `compactLockfree` is not called (`kvstore.go:411-412`).
- **The swap happens only under the batch lock.** The key is reachable only from `W`. `W` is obtained
  only from `LockInsideApply`/`LockOutsideApply` and is returned at `Unlock`: `batchTxSpecG`
  (`InvStore.lean:1162-1214`), and `unlockAt` for the other clients.
  - `SetScheduledCompact` (`store.go:38-42`) and the job's last batch (`kvstore_compaction.go:56-58`,
    `UnsafeSetFinishedCompact` between the limited range and `Unlock`) each hold `W` for the whole
    write.
  - So the key is never in two sessions. This answers round 14's concurrency question again, now for
    the key.
- `mwSwapW`'s shape `□ (W ={⊤}=∗ MW ∗ (MW ={⊤}=∗ W))` is right: one acquisition, one return per
  session.

**N1 (first tier, truth): `mwSwap_of_inv.stmt` is false** (`WiringDraft.lean:115-128`).

The invariant `inv mwN (kbMWW γ.kb γ.bucket ∨ mwKeyW γmk)` only works if `MW` is exclusive. The return
direction (`MW ={⊤}=∗ mwKeyW γmk ∗ R`):
- opens the invariant and must find the key there;
- if it finds `kbMWW` instead, it needs `kbMWW ∗ kbMWW ⊢ False`.

That does not hold:
- For `some d`: `kbMWW` is `∃ f, fkOwn d.γB f` = `monoNatAuthOwn γ.fk ½ f` (`InvBackend.lean:345`).
  Two halves make a valid whole. The third half is in the backend's lock (`fkHalf`), which the law
  cannot see.
- For `none`: `viewFkW` is opaque, so nothing can be proved of it. An exclusivity law for it would be
  an axiom.

Concretely, the law fails in this run:
1. A holder of the key acquires: the key goes into the invariant, and the holder gets the right and
   the return wand.
2. Any frame that holds another half (it is a valid resource) opens the invariant, takes the key and
   leaves its half.
3. The return wand now cannot produce the key.

So the law cannot be proved, and for the duplicable instance it is false.

The flaw is my round-14 option (a), copied exactly. This is churn from round 14's repair, but the fix
is local: two definitions change, and `mwSwapW`, `mwSlotW`'s gating and `SetScheduledCompact.specW`
keep their text.

**Restatement: a toggled ghost.** The key is the lock's half of a boolean ghost variable, and it
records where the right is:

```lean
def mwKeyW (γmk : GName) : IProp GF := ghostVar γmk (1 : Qp).half true
def mwInvW (γ : StoreNames) (γmk : GName) : IProp GF :=
  inv mwN iprop(∃ b : Bool, ghostVar γmk (1 : Qp).half b ∗ if b then kbMWW γ.kb γ.bucket else True)
```

- **Acquire.** The two halves agree on `b = true`. Take the right and set both halves to `false`. The
  return wand captures the lock's half at `false`.
- **Return.** The halves agree on `false`. Put the right back and set both to `true`.
- No exclusivity of `MW` is needed.
- **In `NewStore`.** Before the first `Unlock`, allocate `ghostVar γmk 1 true` and put one half in
  `writerRes` (`mwSlotW`). Keep the other half. After `restore`, allocate the invariant with that half
  and the right.
- **Before round 16.** Prove `mwSwap_of_inv` in the Draft (about 40 lines). It is the cheapest glue,
  and it would have caught N1.

**N3 (first tier, placement): `mwInvW` cannot be in `isStore`.**

The Draft's docstring (`WiringDraft.lean:112`) and the plan (`:1456`) put it there.
- `isStore` reads only logical names: `isStore_withPhys` is `rfl` (`InvStore.lean:3366`). D22 uses
  it in `SnapApplyOptsLemmas.lean` and in two `metricsTxnWrite` proofs.
- `mwInvW γ γmk` names `γ.kb`, `γ.bucket` and the new physical `mk`.

Put it, gated, in `physOk` instead, next to `□ kbWTSupplyM` (F5). `physOk` is per physical names
(`fieldShareAt`) and is what `store.Compact` and the job already read (`Hbk`, `storeStop`).

The same paragraph claims that `updateCompactRev` "takes `mwSwapW (storeW s γ) (kbMWW …)` from
`isStore`" (plan `:1501`). That has a second gap:
- The law gives the swap at `W = mwKeyW ∗ R`. For the real backend, `storeW s γ = lateW d.gx`, and
  reaching `writerRes` inside it needs `storeRegd s γ` (`storeW_get`/`storeW_put`,
  `InvStore.lean:2216-2240`).
- `storeRegd` is no longer in `physOk`: D22's S6 moved it to `writerInv`, where it may be pending
  after a restore.
- Today `updateCompactRev` only meets `W = writerRes` (`kb = none`, `store__updateCompactRev.lean:254`),
  so this is new.

**Restatement.** `physOk` gains `if kbCmp γ.kb then mwInvW γ γ.mk ∗ storeRegd s γ ∗ □ kbWTSupply γ.kb
else True`.
- `NewStore` has `storeRegd` from `storeW_register` at the first `Unlock`.
- A store in compaction mode is never restored (N2), so it stays true.
- The law becomes `physOk s γ o ∗ ⌜kbCmp γ.kb⌝ ⊢ mwSwapW (storeW s γ) (kbMWW γ.kb γ.bucket)`.

**Second tier: the key's name.**
- `mk` is a new field of `PhysNames` and `StoreNames` (D22's structures, S5b). So `withPhys`, `phys`,
  the two `Countable` instances and `store.Restore`'s literal `p'` (`store__Restore.lean:151`) change.
- "Allocated … by `store.Restore` for its new names" (`WiringDraft.lean:101`, plan `:1462`) is
  unnecessary under Q5-3: `d'.cm = false`, so `mwSlotW` is `True` and any name will do.
- List these under D22 (N5).

## F2/F3: `nJobRd`, `compactJobResM`, `compactTokW`

**Good.**
- `compactJobResM kb cm = if kbCmp then kbRT ∗ kbSR else True` (`:133`). It is `True` for every store
  that does not compact (F3 is resolved).
- The job's reader comes out of the `actualMaxReaders` that `NewStore` already takes (`:253`). So
  there is no `actualMaxReaders + 1` (F2 is resolved, as the user chose).
- `nJobRd none = 0` agrees with `kbRT none = True`.
- `NewStore`'s post count `actualMaxReaders - nJobRd kb cm` (`:269`) is the right count.

**N2 (first tier, sufficiency for D22; caused by F2's repair together with Q5-3's scope).**

`store.Restore.spec`'s pre requires only `⌜∃ d, γ.kb = some d⌝` of the **old** store
(`Spec/…/store__Restore.lean`). Q5-3 constrains only the new record `d'`.

Take an old store in compaction mode (`d.cm = true`) that was frozen (`crevFrozen`) and kept its
`storeCloser`. `NewStore` can produce one, and `Restore`'s pre admits it. Then:
1. Its creation gave one `kbRT (some d)` to the job's budget, inside `storeCloser`'s
   `compactQueue γ (-1)`.
2. The readers' pool must have one slot fewer: `poolBody`'s `k + j + w + r = nReaders` (`:3025`) is
   set at `NewStore.lean:464` with `nReaders`.
3. `Restore`'s post promises `nReaders - 1` old `storeRT γ`: `nReaders - 2` from the pool through
   `restore_switch`, plus the writer's one (`store__Restore.lean:378-385`). With the slot missing, the
   pool gives `nReaders - 3`.
4. The missing token is in the queue's abstract `R`. The proof drops that queue
   (`store__Restore.lean:89`, `⟨…, Hq, -, -, -⟩`), and `Scheduler.Stop`'s post is `True`
   (`Scheduler__Stop.lean:35`). So the proof cannot get the token back.

So `store.Restore.spec` as stated becomes unprovable for that store. My round-14 note ("D22's
accounting can recover the job's token from `storeCloser`'s `compactQueue γ (-1)`") was wrong: the
proof cannot use `R` without the queue's `Q`.

The server is not affected, because its stores are all `cm := false`. But the spec quantifies over
every old store.

**Restatement** (the user's, since it touches D22's statement or invariant; call it Q5-4):
- **(a) Recommended. "No restore in compaction mode", applied to the old store too.**
  - The pre becomes `⌜∃ d, γ.kb = some d ∧ d.cm = false⌝ ∗ ⌜d'.cm = false⌝` (Q5-3's premise
    extended).
  - The server must know `cm = false` of its current backend. The pure facts `∃ d, E.γ.kb = some d`
    in `InvApplier.lean` (`:478`, `:554`, `:830`) each gain `∧ d.cm = false`. They hold at boot (the
    literal record) and after `Restore` (`d'.cm = false`).
  - This is a D22 statement change of a few lines, and it is M2's scope restriction stated where it
    applies.
- **(b) No D22 statement change.**
  - The job's budgets (`compactJobResM`) stay in `storeCloser` until `compactRight_of_closer` moves
    them into the queue's `R`. That lemma's statement is unchanged; its proof threads them.
  - `Restore` takes them back from `storeCloser` directly.
  - The pool's sum becomes `nReaders - nJobRd p.kb` (`poolBody`), and `restore_switch`'s count follows
    (`RestoreMoves.lean`).
  - It changes no statement text, but it changes D22's definitions (`storeCloser`, `poolBody`) and two
    of its proofs.

**N5 (second tier, completeness): where the job's reader leaves the pool.** In either option the
plan must say how the pool accounts for the job's reader:
- `poolBody`'s sum becomes `nReaders - nJobRd p.kb` (a D22 definition, no statement text); or
- `NewStore`'s post becomes `retiredAt γ (nJobRd kb cm)` in place of `retiredAt γ 0` (statement
  text).

The first is smaller. Under (a), `RestoreMoves` is otherwise untouched, since the old store has
`cm = false`.

## F4: the contract at `γ.idx = γi`

- Correct: `NewStore.specW`'s premise (`:249`) and post (`:259`) agree.
- For a store that does not compact, the extra conjunct only weakens what the caller must prove.
- `New.spec`/`newWatchableStore.spec` take `γi` (`New.lean`), so the same conjunct goes in.
- `store.Restore` keeps `γ.idx` through `withPhys`, so D22 is unaffected.

## F5: the write-back supply in `physOk`

**Good.**
- One persistent source serves both `store.Compact` (two tokens: `SetScheduledCompact`'s
  `LockInsideApply`, `kvstore.go:213`, and `ForceCommit`, `:216`) and the job (each batch's
  `LockOutsideApply` and `ForceCommit`, `kvstore_compaction.go:52`, `:90`).
- Both are paid from their own steps' receipts (Perennial's `wp_go_step_receipt`).
- `store.Compact.specW`'s pre correctly has no `storeWT`.

**Second tier.** `□ kbWTSupplyM` in `NewStore.specW`'s pre (`:252`) has a redundant `□`: `kbWTSupply
(some d)` is already `□ …`. In this stage nothing establishes it for `cm = true`; the server is
`cm := false` and R2-7 is M2's. So the compaction over the real backend is verified relative to a
premise only M2 discharges. That is acceptable, but say so in `mvcc_NewStore_backend`'s docstring.

## F6: `SetScheduledCompact.specW` (and `SetFinishedCompact`)

**Good.**
- It is over `batchTxSpecG` in full generality, with `Cmp := True`.
- `RT ∗ WT` is in the pre and `RT` in the post. That matches `LockInsideApply`'s clause
  (`InvStore.lean:1162-1164`).
- `mwSwapW W MW` is the minimal way to state it. `MW` cannot be in the pre: it is reachable only
  after the lock (N1/N3).
- The proof's order works: lock, swap, then `metaPutCap (Locked [] ∗ MW)` (`:1229`), return `MW`,
  the hook's update, `unlockAt`.
- The caller gets `Cmp := True` from `isKeyBackendG_cmp` with `storeCmp` (as
  `store__updateCompactRev.lean:238` does today).
- `SetFinishedCompact` has no caller. It is changed for uniformity, which is fine.

**Second tier.** `updateCompactRev.spec`'s "no new premise for the caller" holds only once N3's
`physOk` carries `mwInvW ∗ storeRegd`.

## F7: `isKeyBackendG_weaken.stmt`

- True at arbitrary `SR' SRh' MW'` with `¬ Cmp'`:
  - those three occur only under `⌜Cmp⌝` (`batchTxSpecG` `:1199-1231`; `isKeyBackendG` `:1396-1404`);
  - `Del'`'s only unguarded occurrence is `UnsafeRange`'s post disjunct, which
    `□ ∀ k, Del k -∗ False` makes vacuous.
- It now yields `storeBackend` with `kbSR γ.kb = srSlot d.be` for a non-compacting real store.

## The listed changes: complete? needed?

**Client-visible (mvcc).**
- `store.Compact`, `NewStore`, `New`, `newWatchableStore`, `store.restore`, `SetScheduledCompact`,
  `SetFinishedCompact`, `updateCompactRev` (unfolding only): all needed, and the text is right.
- Missing: under N2 (a), `store.Restore.spec`'s old-record conjunct. Under N5's second option,
  `NewStore`'s `retiredAt`.

**Exported results.**
- `mvcc_NewStore_backend`/`NewStore_backend`, `mvcc_backend_bridge`, `mvcc_storeBackend_of_backend`,
  `storeBackendT_of_backend`, `mvcc_store_Compact`: needed as listed.
- **N4 (second tier).** `server_kv_backend`, `server_kv_watchable` and `server_kv_backend_hooks` are
  generic over `d` (`etcdserver/Results.lean:812`, `hP : bridgeParams d.P` only). Their posts give
  `actualMaxReaders` readers (`:849-850`), which holds only for `d.cm = false`. So either:
  - add `(hcm : d.cm = false)` (smaller; their caller builds `d` with a literal `cm := false`); or
  - write the counts as `actualMaxReaders - nJobRd (some d)`.

  The plan's "their reader counts are unchanged (`cm := false`)" (`:1522`) leaves this implicit.
- `NewServer.spec`: unchanged, which is right.
  - `fkV` comes from `newPost`'s `fkCl` inside `BuildLemmas`.
  - `kbSRM`/`kbWTSupplyM` are `True` at `cm := false`.
  - Q5-2's `srSlot` in `newPost` is an extra resource `NewServer` can drop.

**Trusted.** Unchanged except `storage.OpenBackend` (Q5-2), as listed.

**D22's (the collaborator's).** Not limited to the `KBReal.cm` literals and Q5-3's premise. Also:
- N2 (a): the old-record conjunct, and `cm = false` in `InvApplier`'s three `∃ d` facts; or, under
  (b), `storeCloser` and `poolBody`;
- N5: `poolBody`'s count (or `NewStore`'s `retiredAt`);
- N3: `PhysNames`/`StoreNames.mk` and `withPhys`/`phys`/`Countable`; `store.Restore`'s literal `p'`;
  `RestoreMoves`' `writerRes (γ.withPhys p')`, which gains `mwSlotW` (`True` by `d'.cm = false`).

None of these, except N2 (a), changes a D22 statement's text. They must still be listed, so the
collaborator finds them.

**The server.** Nothing changes beyond D22's literals, N2 (a)'s `InvApplier` facts (if chosen), and
N4's premise on `server_kv_*`. R2-7 and `NewServer.spec` are correctly deferred to M2.

**Still the user's.**
- **Q5-4** (N2): (a) or (b). It touches D22 either way.
- Everything else is the agent's: N1's ghost, N3's placement, N4's premise, N5's option.

## Estimate

The plan's 1100-1400 lines stands, plus:
- N1: about +40, the swap law's proof;
- N3: about +30, `storeRegd`/`mwInvW` in `physOk`, and `PhysNames.mk` at about 6 sites;
- N2: about +50 under (a) (`InvApplier`'s facts, `SnapApply*` discharge), or about +120 under (b)
  (`storeCloser`, `compactRight_of_closer`, `poolBody`, `restore_switch`);
- N5: about +30.

That makes about **1250-1600** lines. One full build per round (1724 modules, 300035 lines,
`etc/importers.py --count InvStore.lean`).

## Ranking (two-tier rubric)

1. **(ii) the write right's home** (`mwKeyW`/`mwInvW`/`mwSwap_of_inv`): N1, which is false, and N3,
   the wrong home and the missing `storeRegd`. Both are first tier and both come from round 14's
   repair.
2. **`store.Restore.spec` under F2/Q5-3**: N2, first tier. The user's choice (Q5-4).
3. **`NewStore.specW`**: correct after F2/F3/F4. N5 (the pool's count) is second tier, and so is the
   redundant `□`.
4. **`server_kv_*`**: N4, second tier.
5. **`SetScheduledCompact.specW`**, **`store.Compact.specW`**, **`isKeyBackendG_weaken.stmt`**,
   **`compactJobResM`/`compactTokW`/`kbWTSupplyM`**: no finding. Second-tier notes only.
