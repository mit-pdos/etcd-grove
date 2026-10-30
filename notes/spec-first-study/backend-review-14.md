# backend-cmp, Review round 14 (2026-10-29): question 5's Draft (the wiring)

**Under review.** Commits `723e49c9d2` (the Draft: `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/
WiringDraft.lean`, imported by nothing, and the plan's "Question 5: the wiring, the user's decisions"
and "Question 5's Draft round") and `d271523c8e` (the user's answers Q5-1 and Q5-2, notes only).
`HEAD` is `d271523c8e`, so no finding is stale. The Draft file still has the pre-Q5-1 shape
(`kbCmpW := True`, `kbCmpM` with the mode as a parameter). I judged every statement **with the
answers applied**: `KBReal.cm`, `kbCmp (some d) := d.cm`, `srSlot` in `newPost`/`newPostK`.

This is the **first** round of this increment, so the stop rule does not apply yet. None of the
first-tier findings comes from a previous repair: they are in the new design, so this is not churn.

**Read.**
- `WiringDraft.lean` (whole) and the plan sections the commits add.
- `InvStore.lean`:
  - `KBReal` (`:81`), `bkNoCmp`/`viewNoCmp`/`kbNoCmp`/`kbMW` (`:479-503`);
  - `batchTxSpecG` (`:1155-1245`), `batchTxInitSpec`, `batchTxSpec`, `isKeyBackendG` (`:1369-1405`);
  - `kbRT`/`kbWT`/`kbSR`/`kbWTSupply`/`compactJobRes` (`:1512-1558`), `kbCmp` (`:1672`);
  - `compactTok`/`compactQueue`/`compactRight` (`:1822-1870`);
  - `compactRes` (`:2094`), `writerRes` (`:2141`), `lateW`/`storeW`/`kbWi` (`:2170-2200`);
  - `storeW_register` (`:2250`), `writerReg` (`:2279`), `physOk` (`:2822`);
  - `storeBackend`/`storeBackendT` (`:3427-3446`), `storeCloser` (`:5097`).
- `BackendBridge.lean`: the statements of `isKeyBackendG_of_backend` (`:2541-2571`),
  `isKeyBackendG_of_backendC` (`:3155-3192`), `storeBackendT_of_backend` (`:3326-3360`) and
  `storeBackend_of_backend` (`:3428`).
- The backend: `InvBackend.lean` (`fkOwn`, `fkV`, `fkCl` at `:340-365`; `dlReg`/`dlNoDel`/`dlIs` at
  `:536-560`), `DelKeys.lean` (`dlInit`, `srSlot`/`srHeld`), `InvNew.lean` (`newPost` at `:58-68`,
  `newPostK`), and `Image.lean` (`bkNoCmp_of_fkCl`, `fkV_of_fkCl`, `bkNoCmp_fkV_of_fkCl`).
- Specs: `store__Compact`, `store__updateCompactRev`, `NewStore`, `store__Restore`,
  `SetScheduledCompact`, `store__Close`.
- Proofs:
  - `NewStore.lean` (the step comments, `:95-340`);
  - `store__Restore.lean` (`:170-310`), `mvcc/Results.lean` (`:218-400`);
  - `etcdserver/BuildLemmas.lean` (`:35-130`), `SnapApplyWalk.lean` (`:280-400`), `SnapApplyDefs.lean`
    (`:60-70`);
  - `InvApplier.lean` (`srvWTPool` `:816`, `srvWTPool_take_at_d` `:951`, `srvWTPool_take_extra_d`
    `:1037`), `CompactMode.lean` (header).
- Perennial's `RWMutexGuard.lean` (`ownRWMutex`: one reader slot of `actualMaxReaders`).
- Go at the pin (`/shared/etcd-grove/.lake/go-src/etcd/server/`):
  - `storage/mvcc/kvstore.go`: `NewStore` (`:87-134`), `updateCompactRev` (`:197-222`),
    `checkPrevCompactionCompleted` (`:225-231`), `compact`, `Compact` (`:272-282`), `restore`
    (`:317-`);
  - `storage/mvcc/kvstore_compaction.go` (`:28-105`) and `storage/mvcc/store.go` (`:38-60`);
  - `storage/backend/backend.go` (`safeRangeDeleteMu` `:138-140`, `defragNonBlocking` `:694-700`,
    `LockForSafeRangeDelete` `:1115`) and `storage/backend.go` (`OpenBackend` `:75-100`);
  - `etcdserver/apply/backend.go:73` (the only caller of `KV().Compact`).

**Checked.**
- `etc/importers.py --count InvStore.lean`: 1724 modules, 299962 lines, which confirms the plan's
  "1723 rebuilt".
- `--uses` for each changed name: `kbMW`, `storeW`, `compactTok`, `kbCmp`, `storeCmp`, `kbNoCmp`,
  `viewNoCmp`, `writerRes`, `lateW`, `storeBackend`, `storeBackendT`, `physOk`, `compactJobRes`,
  `storeCloser`, `KBReal` (the list is under "Proof sites and estimate").
- No build. No Go bug found; `issues/` needs no entry.

## Summary

Seven first-tier findings, in four targets, plus one in R9-3:

| # | target | finding |
|---|---|---|
| F1 | (ii), `storeWW` | the write right cannot reach the batch lock where the Draft puts it |
| F2 | `NewStore.specW`, `compactTokW`/`compactJobRes` | the job's reader token has no source |
| F3 | `NewStore.specW`, `compactJobRes` | the budgets are not gated by Q5-1's mode, so no non-compacting caller can supply them |
| F4 | `NewStore.specW` | the backend-contract premise does not fix `γ.idx = γi`, so the registration cannot meet it |
| F5 | `store.Compact.specW` | the write-back tokens are missing |
| F6 | R9-3 | "a general `MW`" is not enough: the whole `batchTxSpecG` must be general |
| F7 | `isKeyBackendG_weaken.stmt` | the conclusion fixes `SR`/`SRh` to `True`, which does not fit `storeBackend` under Q5-1 |

Your concurrency question about (ii): **the batch lock is a sound home for the write right, but the
right cannot get there the way the Draft says (F1).**
- `SetScheduledCompact` (`store.go:38-42`, from `kvstore.go:213`) writes in a `LockInsideApply`
  session. The job writes `UnsafeSetFinishedCompact` (`kvstore_compaction.go:56-71`) in a
  `LockOutsideApply` session. Both are serialized by the batch lock, so a right that is taken at
  lock time and returned at `Unlock` is never in both places.
- But `NewStore`'s first `tx.Unlock()` (`kvstore.go:124`, the deposit `NewStore.lean:335-339`) runs
  **before** `s.restore()` (`kvstore.go:129`). `restore` is what gives the half back. So the half
  does not exist yet when the deposit happens.

The rest:
- **True and usable:** `store.Compact.specW`'s read-token loan; `isKeyBackendG_congrDel.stmt`;
  `delKeyI`/`storeDlReg`; (iii); R2-7's law.
- **R2-7 is already proved:** its law is `srvWTPool_take_extra_d` at `dq := DFrac.discard`.
- **Probably not needed in this stage:** under Q5-1, NewServer can stay non-compacting
  (`cm := false`). Then R2-7, the discard of `E.γbe`, and `NewServer.spec`'s change belong to M2.
- **Proof-site list and estimate:** the list misses about eight files, and 700-900 lines is low. I
  estimate about 1200-1600 lines.

## Per target

### (ii) The write right's home: `storeWW s γ := storeW s γ ∗ kbMWW γ.kb γ.bucket`

**Good.**
- Your question, whether the batch lock is sound with `SetScheduledCompact` running while the previous
  job runs: **yes**. Both writes of a compaction key run inside batch-lock sessions, so the lock
  serializes them.
- The rejection of the compaction token as the home is right. The job is asynchronous (`compact`
  schedules it, `kvstore.go:234-270`), so the queue can hand the token to job *k* while
  `store.Compact` for job *k+1* is already in `SetScheduledCompact`.
- Other backend clients (the lessor, auth) also lock this batch transaction. They get `W` only for
  their own session and must return it at `Unlock` (`unlockAt … W`). So a right inside `W` is never
  kept by another client.

**F1 (first tier: sufficiency, and the proof plan is impossible as written).**
- The Draft says `NewStore` "deposits it with `W` at its first `Unlock`". In Go, `NewStore` runs
  `tx.LockOutsideApply(); …; tx.Unlock()` (`kvstore.go:121-124`), then `s.b.ForceCommit()`, and only
  then `s.restore()` (`:129`).
- `restore` holds `kbNoCmp` through its `ReadTx` reads. Its post is where the half comes back
  (`kbNoCmpW_MW`).
- After `restore`, `NewStore` never takes the batch lock again. `NewStore.lean:335-339` registers
  `writerRes` at that first `Unlock` (`storeW_register`, `InvStore.lean:2250`).
- A second, independent problem: as the contract's `W`, `storeWW` cannot be met by the real backend.
  - The real backend's lock holds what it was created with: `isBackend d.γB d.P (lateW d.gx) …`
    (`BackendBridge.lean:3352`, `Results.lean:263`).
  - The bridges pass that `W` through unchanged (`isKeyBackendG_of_backendC`, `:3184-3192`:
    `… W W …`).
  - So `storeWW (some d) = lateW d.gx ∗ ∃ f, fkOwn …` is not the lock's resource. The creator cannot
    put the flag's half into the lock either: it must give `bkNoCmp` (the same half) to `NewStore`
    for `restore`.
- **Affects:** `NewStore`'s proof; `storeBackend`/`storeBackendT`/`physOk`, whose `W` must be what
  the lock really holds; `store.Restore` (D22).

**Restatement.** Keep `storeW` as it is: it is the lock's resource, and for the real backend it is
fixed at creation. Give the right a home that `NewStore` can reach *after* `restore`. Two options
that keep it "in the store" (decision (ii)):
- (a) **An invariant shared with the lock.**
  - Before the first `Unlock`, allocate a lock key `mwKey γ` (exclusive) and put it in `writerRes`
    (or in `compactRes`, which is already "the meta keys' record").
  - After `restore`, allocate `inv mwN (kbMWW γ.kb γ.bucket ∨ mwKey γ)` with the right. Its persistent
    fact goes in `isStore`.
  - A session that writes a compaction key holds the lock, so it holds `mwKey`. It swaps the key for
    the right, writes, and swaps back before `Unlock`.
  - The only session before the invariant exists is `NewStore`'s own.
- (b) **D22's pending-deposit pattern** (`writerReg`, `InvStore.lean:2279`).
  - The right waits in `s.mu`'s resource until the first `store.Compact`. That call holds `s.mu`
    exclusively and the batch lock in `SetScheduledCompact`, and moves the right into `writerRes`
    once, leaving a persistent witness that the job gets through the queue.
  - Every job runs after at least one successful `SetScheduledCompact`.

(a) is smaller and touches no D22 statement.

**Consequence for D22.** If the right ends up in `writerRes` (in option (a) it is the key that does),
`store.Restore` does not "drop" it. It deposits the half that `restore` returns into the new store's
pending `writerReg`; it has that half (`store__Restore.lean:184`, `:297`). The plan's "`store.Restore`
drops it" holds only for a home outside `writerRes`. Fix the plan's sentence to match whichever option
is chosen.

### `NewStore.specW`

**Good.**
- The post is today's.
- `kbNoCmpW` covers both backends.
- Taking the index's names `γi` as a parameter, already allocated (`idxFresh γi`, post
  `⌜γ.idx = γi⌝`), is what makes `storeDlReg` possible.

**F2 (first tier: sufficiency; no caller can establish the pre).** The job's reader token in
`compactJobRes kb` (`kbRT kb`, `InvStore.lean:1557`) comes on top of the
`replicate actualMaxReaders (kbRT kb)` the pre already takes (`Spec/…/NewStore.lean:92`).
- A real backend has exactly `actualMaxReaders` reader tokens: `newPost`, `InvNew.lean:62`. `rdTok`
  includes an `ownRWMutex` reader slot of `readTx.mu`, bounded by the guard's
  `ownTokAuthDfrac γmax DFrac.discard actualMaxReaders` (Perennial `RWMutexGuard.lean:127-132`).
- `NewServer` passes all of them to `New` (`NewServer.lean:508` → `:583`; `BuildLemmas.lean` pre).
- So for `kb = some d` the pre asks for `actualMaxReaders + 1` tokens. The same goes for
  `mvcc_NewStore_backend` and `server_kv_*` with the plan's "`compactJobRes (some d)`" added.
- **Affects:** `mvcc_NewStore_backend`, `NewStore_backend`, `server_kv_*`, `NewServer`.
- **Restatement.** `NewStore` gives the job one of the `actualMaxReaders` it already takes, so the pre
  carries only `kbSR kb ∗ kbWTSupply kb` (gated, F3). The post returns
  `replicate (actualMaxReaders - 1) storeReaderC` (or keeps the count only when not compacting; F3).
  - `New`/`newWatchableStore`'s posts change their reader counts with it (`watchReader … - 2` becomes
    `- 3`).
  - D22's accounting (`store.Restore`'s `nReaders - 1` "for the old backend's `Close`") can recover
    the job's token from `storeCloser`'s `compactQueue γ (-1)`, whose `R` is still the token itself
    when nothing was compacted.
  - Say which in the plan; this changes `New.spec`'s post.

**F3 (first tier: no unneeded premise / sufficiency; Q5-1 not applied).** The pre takes
`compactJobRes kb` unconditionally.
- Under Q5-1, every non-compacting real store must still supply it: today's `NewServer`, D22's paths,
  every `server_kv_*` user.
- That includes `kbWTSupply (some d)` = `□ (⧗ 1 ={⊤}=∗ wbTok d.γB)`. Per R2-7, the server can give
  this only after discarding its part of `E.γbe`, which a server that installs snapshots must not do.
- The storeCloser's queue holds `compactTokW γ (-1)` for every store, so the deposit is unconditional
  too.
- **Restatement.** Gate by the mode: `compactJobRes (some d) := if d.cm then kbSR ∗ kbWTSupply (∗ the
  reader token, F2) else True`. Then `compactTokW`'s budgets are `True` for every store that never
  compacts. This is the "one spec, a gated row" principle, with the mode in the state as Q5-1 wants.

**F4 (first tier: sufficiency for the compacting creator).** The backend-contract premise is
`∀ s γ, ⌜γ.bucket = γb ∧ γ.kb = kb⌝ → storeBackend b s γ P`.
- For a compacting store, `storeBackend`'s `Del := delKey γ = delKeyI γ.idx` comes from the
  registration `storeDlReg d.γB γi` through `isKeyBackendG_congrDel`.
- That registration was fixed at one `γi`, so the creator can prove the contract only for
  `γ.idx = γi`, not for every `γ`.
- **Restatement:** `∀ s γ, ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ → storeBackend b s γ P`. The
  same constraint goes into `storeBackend_of_backend`'s compacting form and `BuildLemmas`.
  - `NewStore`'s proof meets it: its post already says `γ.idx = γi`.
  - `store.Restore`'s `γ.withPhys p` keeps `γ.idx`, so D22 is unaffected.

### `store.Compact.specW` (i)

**Good.**
- The loan of `storeRT γ` is right and minimal.
- `checkPrevCompactionCompleted` (`kvstore.go:225-231`) runs before `updateCompactRev` on every path
  (`:274`), so every branch needs it and every branch returns it.
- The only caller is the apply thread (`etcdserver/apply/backend.go:73`), which holds `writerOwn`.
- The same token also covers the `RT` lent to `LockInsideApply` and `ForceCommit`.

**F5 (first tier: sufficiency for the real backend).** Over `some d` with `d.cm`, `updateCompactRev`
makes two calls that need a write-back token:
- `SetScheduledCompact`'s `LockInsideApply` (`batchTxSpecG`, `InvStore.lean:1162`:
  `{{ Pre ∗ RT ∗ WT ∗ … }}`);
- `s.b.ForceCommit()` (`kvstore.go:216`; `isKeyBackendG`, `InvStore.lean:1390`:
  `{{ RT ∗ WT ∗ X ∗ Req X Y }}`).

Today `storeWT γ = True` only because `storeCmp` forces `kb = none`. The draft's pre has no
`storeWT`, and the budgets in the compaction token are not reachable from here: the token is in the
queue, possibly held by the running job.
- **Affects:** `store.Compact`, `updateCompactRev`, `mvcc_store_Compact`, and the apply thread's
  compaction glue on `m2`.
- **Restatement**, either of:
  - add `storeWT γ ∗ storeWT γ` to the pre (consumed). The apply thread pays them with
    `srvWTPool_take_extra` (`InvApplier.lean:1059`), two receipts.
  - move the persistent `kbWTSupply` out of the token into `physOk`/`isStore`, where both
    `store.Compact` and the job pay from the receipts of their own steps. This also shrinks
    `compactJobRes` to its exclusive parts. I prefer this one: one source for both, and no new
    caller burden.

### R9-3: `SetScheduledCompact.spec` / `SetFinishedCompact.spec` "with a general `MW`"

**F6 (first tier: sufficiency).** Both take `mvcc.batchTxSpec` (`Spec/…/SetScheduledCompact.lean`),
which fixes `RT = WT = True` and `PutOk := noPutCond` as well as `MW := kbMW none`
(`InvStore.lean:1290`). Over the real backend, `RT` is `bkRTx`, `WT` is `wbTok`, and `PutOk` is
`keyPutOk`.
- **Restatement:** state them over `batchTxSpecG bt View RT WT PutOk Del W Dep True Locked P HF Rb MW`,
  all general, with `RT ∗ WT` in the pre and `RT` in the post.
- `SetFinishedCompact` has no caller in the server (`grep`: only `store.go:50`). Its change is for
  uniformity only.

### `isKeyBackendG_weaken.stmt`

**Good.**
- True as a law. `Del` occurs only covariantly outside the `⌜Cmp⌝` clauses: `UnsafeRange`'s post
  disjunct, and `snapThin` in `keyReadSnap`.
- The only contravariant occurrence (the compacting range's `UnsafeDelete` pre) is under `⌜Cmp⌝`.
  With `□ ∀ k, Del k -∗ False` the covariant uses are vacuous, so any `Del'` works.
- `dlNoDel`, together with `dlReg`'s flag at `true`, gives the premise without a later.

**F7 (first tier under Q5-1: sufficiency for `storeBackend`).** The conclusion fixes
`SR SRh := True`, but `storeBackend`'s slots become `kbSR γ.kb`/`kbSRh γ.kb` (plan). For a
non-compacting real store (`cm = false`) that is `srSlot d.be`, not `True`. So the weakened old bridge
does not produce `storeBackend` for the stores Q5-1 keeps on it.
- `SR`, `SRh` and `MW` occur only under `⌜Cmp⌝` (`isKeyBackendG` `:1396-1404`; `batchTxSpecG`'s
  `MW` only in its `⌜Cmp⌝` clauses).
- **Restatement:** the conclusion at arbitrary `SR' SRh' MW'`:
  `… ⊢ isKeyBackendG b … Del' W Wi Dep Cmp' P HF Req Rb Bt SR' SRh' MW'`.

**Second tier.**
- The old bridge as a corollary of the new one inherits the new one's premises: `hHK`, `hFV`, and
  `fkV γ true` (`BackendBridge.lean:3182-3188`).
- So `mvcc_backend_bridge` (`Results.lean:218`, generic `P`) gains `hHK`/`hFV`/`fkV`, and so do
  `storeBackendT_of_backend` and `storeBackend_of_backend`.
- The proof sites that must supply `fkV`:
  - `SnapApplyWalk.lean:394` uses `bkNoCmp_of_fkCl`; `bkNoCmp_fkV_of_fkCl` gives both.
  - `BuildLemmas.lean` gets only `bkNoCmp`, not `fkCl`, so `server_kv_*` gain `fkV` even when not
    compacting.
- The plan lists `fkV` for `NewStore_backend`; list it for the bridge results too.

### `isKeyBackendG_congrDel.stmt`

**Good.**
- True and usable.
- `bkDel k = dlIs γ ("key", k)`. Saved-predicate agreement under `▷`, plus the timelessness of
  `delKeyI`, gives `bkDel k ⊢ ◇ delKey γ k`, and `delKeyI` gives `bkDel` directly. So the statement's
  `Del k ∗-∗ ◇ Del' k` is the right shape.
- Contravariant uses (`UnsafeDelete`'s `Del k`) need only `Del' k ⊢ ◇ Del' k ⊢ Del k`.
- Covariant uses sit under triple posts, so a fupd strips the `◇`. The one nested `□ ∀` (`snapThin`,
  `InvStore.lean:642-644`) goes through `except_0_forall`/`except_0_persistently`: `snapThin m m' Del ⊢
  ◇ snapThin m m' Del'`.

**Second tier (cost).** The proof walks every nested triple of `isKeyBackendG`, `isBatchTxG` and
`keyReadSnap`, including the limited range's `U`-indexed clauses. 180 lines for both laws looks low;
`congrDel` alone is likely 200 or more.

### (iii) `viewFkW` / `viewNoCmpW` / `kbNoCmpW` / `kbMWW`, `kbNoCmpW_MW`

**Good.**
- Opaque, so not an axiom: no trust-base change.
- It makes the assumed instance satisfiable by an honest creator, and the one law is proved.
- `kbMWW none` is existential over `f`, so a holder cannot recover `viewFkW γb 0` after a put.

**Second tier.** `batchTxSpec` fixes `MW := kbMW none` (`InvStore.lean:1290`). With `kbMWW` over
`γb`, it gains a `γb` parameter; with F6, `SetScheduledCompact` no longer uses it.

### `compactTokW`, `compactJobRes`, `kbSR`/`kbSRh`

- First tier through F2 and F3 (the reader token, the gating).
- **Second tier:** `kbWTSupply` is persistent. It does not need to travel in an exclusive token, and F5
  wants it elsewhere.
- `srSlot` = one guard slot (`ownRWMutex`, one of `actualMaxReaders`). Q5-2 should say that `newPost`
  gives one. Defragmentation (`defragNonBlocking`, `backend.go:694-700`, the writer) is out of scope.

### `delKeyI` / `storeDlReg`

**Good.**
- `delKey_eq_delKeyI` is `rfl`.
- Fixing the registration before `NewStore` is possible because `γi` is allocated first.
- The saved predicate's `⌜nk.1 = keyName⌝` matches `bkDel`'s `("key", k)`.
- Only F4's quantifier is missing.

### R2-7's law: `srvWTPool E γp ∗ dghostVar E.γbe DFrac.discard d ⊢ □ (⧗ 1 ={⊤}=∗ wbTok d.γB)`

**Good.**
- True, and already proved in substance: it is `srvWTPool_take_extra_d E γp d DFrac.discard`
  (`InvApplier.lean:1037-1057`) under `□`, since both premises are persistent.
- That proof needs `n ≥ 1`. It gets it from `receipt_add_one_lt` and `receiptBound ≤ a + n + 1`.
- A discarded part agrees with the pool's own quarter.

**Second tier (minimality).**
- Under Q5-1, nothing in this branch's server compacts: `CompactMode.lean` is the reversed M2 round-1
  family, and `ρ.kv.cmp` is on `m2`.
- With F3's gating, `NewServer` can create its backend with `cm := false` and need no `kbWTSupply`.
- So R2-7, the boot-time discard of `E.γbe`, and `NewServer.spec`'s change belong to M2's merge, not
  to this stage. Deferring them removes the top-level statement change and the D22-side edit
  (`InvApplier.lean`) from this increment.

### Q5-1 (`KBReal.cm`) as applied

**Good.** One family; D22's records gain only a field.

**Second tier.**
- `SnapApplyWalk.lean:288` builds the received record as `{ d with γB, be, gx }`, which *inherits*
  `d.cm`. `SnapApplyDefs.lean:66-69` builds it field by field.
- Both must say `cm := false`, or both `cm := d.cm` together with a fact that the restoring server's
  `d.cm = false`. The first is simpler.
- `cm := false` means a store loses `storeCmp` across `store.Restore`. That is M2's "no restore in
  compaction mode", a scope restriction: cite it in `kbCmp`'s docstring.

## Exported results: complete? needed?

Needed, as listed:
- `mvcc_NewStore_backend`, `NewStore_backend`: F2, F3 and F4 apply to their pre.
- `mvcc_backend_bridge`, `mvcc_storeBackend_of_backend`: these gain `hHK`, `hFV` and `fkV` (F7's
  second tier).
- `mvcc_store_Compact`: same text, but its meaning grows with F5 (the WT, if added to the pre).
- `server_kv_backend`, `server_kv_watchable`, `server_kv_backend_hooks`: `fkV` and the reader count.

Missing from the list:
- `SetScheduledCompact.spec`/`SetFinishedCompact.spec` (F6).
- `updateCompactRev.spec` (F5).
- `New.spec`/`newWatchableStore.spec` posts' reader counts (F2).

Not needed in this stage: `NewServer.spec` (see R2-7).

Decisions beyond Q5-1/Q5-2 to put to the user, batched:
1. **Where the write right lives** (F1). The Draft's home is unreachable; option (a) or (b). This is
   within (ii)'s "stays in the store", so the agent can decide it, but record it as decided by the
   agent.
2. **The job's reader token** (F2). It comes out of the store's own `actualMaxReaders`, changing
   `New.spec`'s post. Choose between always (one spec, the uniform count) and only when `cm` (a
   mode-dependent count).
3. **Defer R2-7 and `NewServer.spec` to M2.** This reverses part of the approved (iv), so it is the
   user's call.

No new axiom or family. The trust base changes only by Q5-2 (already approved; `OpenBackend` gets
the `axiom` skill again).

## Proof sites and estimate

Missing from the plan's list (`etc/importers.py --uses … --files`):
- in `InvStore.lean`: `physOk` and `storeBackendT`, beside `storeBackend`;
- `RestoreMoves.lean` (`writerRes`, `kbNoCmp`);
- `etcdserver/SnapApplyOpen.lean` (`lateW`);
- `Spec/…/New.lean` and `newWatchableStore.lean` (`kbNoCmp`, the counts);
- `SetScheduledCompact`/`SetFinishedCompact`/`UnsafeSet*` specs and proofs (F6);
- the `store__updateCompactRev` spec (F5);
- `SnapApplyWalk.lean` (`fkV`, `cm := false`).

With F1-F7, my estimate is about **1200-1600 lines**, against the plan's 700-900:
- the write right's new home: +100-200;
- the WT through `store.Compact`/`updateCompactRev`: +50-100;
- R9-3 made general: +50;
- reader counts through `New`/`BuildLemmas`/D22's `Restore`: +100-200;
- the two laws: nearer 300 than 180.

One full build per round stands (1724 modules).

## Ranking (two-tier rubric)

1. **`NewStore.specW`** (with `compactJobRes`/`compactTokW`): three first-tier findings (F2, F3, F4).
   The pre cannot be established for a real backend in either mode.
2. **(ii) `storeWW`**: first tier (F1). The design's deposit point does not exist in the Go order,
   and the contract's `W` is not the real lock's.
3. **`store.Compact.specW`**: first tier (F5), the WT is missing. Its (i) part is right.
4. **R9-3**: first tier (F6), under-generalized.
5. **`isKeyBackendG_weaken.stmt`**: first tier (F7), with a one-line fix; second tier, the premise
   growth of the old bridge.
6. **R2-7's law**: true and already proved; second tier, defer it.
7. **`isKeyBackendG_congrDel.stmt`**, **`delKeyI`/`storeDlReg`**, **(iii)**, **`kbSR`/`kbSRh`**: true and
   usable. Second-tier notes only.

**Stop rule.** This is round 1 of the increment, so repair and review again. If the same statements
(`NewStore.specW`, the write right's home) still draw first-tier findings after round 16, send the
questions to the user, or write `NewStore_backend`'s glue against the real caller.
