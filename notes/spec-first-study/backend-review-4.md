# backend-cmp, Review round 4 (2026-10-29)

**Commit under review.** `f18481f78a` (branch `backend-cmp`). The changes since round 3 are
`ddeadfe227..f18481f78a`, five commits:
- `5b9e4b5d94`: round 3's docstrings;
- `0bd34c698f`: `safeSt` in place; `UnsafeSeqPut.specC` and `safeStC` folded;
- `e7441beb7c`: the readers' side over the logical view;
- `0e2ed781bb` and `f18481f78a`: O1's fallback, then the flag `dlb`.

Round 3's report is `notes/spec-first-study/backend-review-3.md`. The decisions are in
`notes/backend-cmp-plan.md`: "The thin-view Draft round" and "Decided by the agent while the user
was away".

**Go.** Read at the pin: `/shared/etcd-grove/.lake/go-src/etcd/server/storage/backend/`.

**Build.** Every `.olean` of the 29 changed `.lean` files is newer than its source in the worktree,
so the round compiled. I did not build. I did not run `etc/tcb-report.py`, because it writes
`.lake/tcb.json`. So the agent's claim "no `sorry` of this stage under any result" is
**uncertain** here.

What I did check: the five `sorry`s left are all in `isKeyBackendG_of_backendC`
(`BackendBridge.lean:2293, 2295, 2321, 2325, 2352`), and nothing outside its own file names that
theorem. "Verified" below means read in Go or in the Lean source. I proved nothing new.

## Summary

The readers' side of the thin view is **true of Go**, and its proofs are complete. A reader's
state never misses a key that is not registered deletable (Target 1). The flag `dlb` is a sound,
later-free way to say "nothing deletable". `sessWf_C_in_S` and the new put premise are true of
Go and weaker than before (Target 3).

What needs revision:

- **R4-1 (the user's call; one spec per function, forward).** `dlNoDel` puts the
  compactor-off mode into top-level statements: `mvcc_NewStore_backend` and the server's
  `server_kv_*` results. `NewServer.wp_proofM` fixes the flag false unconditionally.
  - M2's compactor-on `NewServer.specCompact` (a `sorry` on `lean`) will need these statements
    restated, or a second family.
  - It also departs from the user's F6/F7 route ("`dlInit` kept unfixed"), and the notes record
    it as decided.
  - Taking `dlInit` instead would keep these statements mode-free.
- **R4-2 (complete, forward for group 2).** `Unlock.specC`'s clients'-view branch still returns
  the physical writer's contents (`sData P st.S`), not the logical view. Plan 3.2's `relog` is
  missing from the statement.
  - The write-back and the commit's window case reset the logical view to the physical one in
    the same way (`rtRes_wb_close`, `rtRes_cm_close`).
  - All three must move together in group 2, or a put session after a compaction drops the
    compacted keys from the clients' logical bucket.
- **R4-3 / R4-4 (forward simplifications).**
  - `thinV_rebase` does not need its "commit kept the view" hypothesis. Without it, it is the
    lemma group 2's deleting commit needs.
  - The old bridge's fold is no longer `congrDel` at `False`: `dlNoDel` excludes any `dlReg`. It
    is monotonicity in `Del` and `Cmp`, which `isKeyBackendG`'s shape allows.
- **R4-5 (docs).** Three stale texts.

## Round 3's findings at `HEAD`

| | Status |
|---|---|
| R3-1 (the fold list incomplete: the mvcc-side twin, `congrDel`, `Cmp`) | **Partly addressed**: the plan's "after round 3" paragraph lists the mvcc twin and `Cmp`. The `congrDel` step is now the wrong tool (R4-4). |
| R3-2 (`batchLimitOk`'s placement: the user's) | **Closed**: the decisions entry now reads "the premise placed on every store by the agent ..., accepted by the user after review round 3" (`notes/decisions.md:25295`). |
| R3-3 (`batchTxSpecG`'s stale "Compaction" paragraph) | **Fixed** (`InvStore.lean`, the paragraph before `def batchTxSpecG`): it tells the `Locked []` → `U (limit + 1)` story. |
| R3-4 (`batchLimitOk`'s docstring; `etcdserver/Results.lean:792`) | **Fixed**: "loops forever", and `batchLimitOk` in the server's docstring. |
| Round 3's forward note (`Del := ◇ delKey`) | Unchanged. The flag does not touch mvcc's compacting case: `delKey` stays late-bound, behind `◇`. |

## Target 1: the readers' view over `L` (`rtCore`/`rtRest`/`rtResAt`/`rtRes`/`rtHeld`, `viewQ`, `cacheValid`, `ConcurrentReadTx.spec`, the commit path)

### Is it true of Go?

**Yes. A reader's state can miss only a key compaction deleted.** It can hold an extra key, but
only one the logical view still has, with the same value. The reasoning, all verified in Go:

1. **What a reader sees.** It sees the bbolt read transaction of the current interval plus a copy
   of the read buffer.
   - The copy is the live buffer: `ConcurrentReadTx` holds `readTx.RLock` throughout
     (`backend.go:302-303`), so no write-back or commit runs while it copies.
   - Or it is the cache, reused only when `txReadBufferCache.bufVersion == readTx.buf.bufVersion`
     (`backend.go:320-346`).
   - The copy is deep: `unsafeCopy`/`CopyUsed`, `tx_buffer.go:139-150, 249-258`.
2. **What changes the read buffer.** Every write-back increments `bufVersion`
   (`tx_buffer.go:114`). A commit's `readTx.reset()` empties the buffer but does **not** increment
   it (`read_tx.go:133-138`, `batch_tx.go:397`). So a cached copy at the current version is a
   buffer from earlier in the same version, combined with a later bbolt transaction. That is the
   model's `(rv.1, rv'.2)` in `cacheValid`, with `histAt γ ver i`, `i ≤ idx`.
3. **Every write-back is followed by a version bump.** Every operation that changes something
   increments `pending`: `UnsafePut`/`UnsafeSeqPut` (`batch_tx.go:190`), `UnsafeDelete` (`:246`).
   `Unlock` writes back whenever `pending != 0` (`:329-332`). So within one version the buffer
   only shrinks (commits), and a stale cached copy holds only puts that the later bbolt
   transaction also holds, unless a delete removed them in between.
4. **Deletes.** They are never buffered (`batchTxBuffered.UnsafeDelete`, `batch_tx.go:418-421`).
   - Under `bridgeParams` the only bucket in the view is `Key` (`BackendBridge.lean:101-106`:
     every other bucket is `HB`).
   - On a compacting backend the only deletes of `Key` are compaction's: the lessor deletes from
     `Lease`, which is `HB`. D22's restore paths delete only non-SB buckets and run only without
     compaction.
   - So a key missing from a reader's state is one compaction deleted. That is `thinV`'s second
     clause, with the registration at `delKey`.
5. **The extra keys.** A cached copy from before a compaction commit may still hold a key the
   commit deleted, e.g. a tombstone put and compacted within one commit interval: the
   `cacheValid` docstring's case. The logical view keeps compacted keys (plan 3.2: compaction
   leaves `L` unchanged), and revisions are never re-put, so the value agrees. `thinV`'s first
   clause holds.

**The window.** This is the interval between `Unlock`'s write-back and its commit
(`batch_tx.go:330-356`; `commit` relocks, `:376`). A `ConcurrentReadTx` there sees the old bbolt
transaction and the new buffer.
- For a compaction session the buffer gained only the `Meta` put, which is `HB`, and the deletes
  are invisible. So that state is the old view, `⊆ L`.
- The model's window is something else: it exists only for a session that deposited the clients'
  whole share (`wb_core`'s `if win … bView γ 1`). A compaction session holds none, so it never
  opens one, and readers in that interval are covered by the ordinary write-back state.

### What is good

- **`thinV`'s direction is right**, and the definition is minimal: physical `⊆` logical, plus the
  missing keys deletable. The persistent `□ ∀ nk, … -∗ dlIs γ nk` is the right form for concurrent
  readers.
- **`cacheValid` thin costs a non-compacting reader one law.** Every reader that needs exactness
  holds `dlNoDel` and calls `thinV_exact` (`DelKeys.lean:102`), with no later and no resource:
  `bridge_crt`, `bridge_rt`, `bridge_rt_clean` (`BackendBridge.lean:1364, 1422, 1474`).
  - `ConcurrentReadTx.spec` has no other caller (`grep`: the bridge and `Link.lean`).
  - `rtHeld_view`/`rtHeld_clean` now give their resources back. They are internal laws (the
    backend has no `etc/api` list), so this is fine.
  - Exactness is not "lost for free". It is recovered at a cost of about one line per exact
    reader.
- **`viewQ`.** The readers' quarter is the ghost share at `L` plus `thinV phys L`. Its split law
  makes `thinV` travel with each half. `viewQ_exact` is the law for exact holders. The two
  halves' meaning, ghost agreement on `L` and a persistent thinness fact, is the right
  factorisation: only the agreement needs the fraction.
- **`rtRes_cm_close`'s two cases are right for this round.**
  - **No window.** `L` is kept. The new state is thin through `hview` and the old `Hth`. Cached
    states rebase through `thinV_rebase` (`ReadSide.lean:613-627`).
  - **Window.** The clients' whole share comes back from `cacheInv`, all three shares move to the
    new physical view (`view_upd3`), and `cacheValid` restarts. The older index is poisoned
    (`hwin0`: in a window `idx = 0`, so `i ≤ idx + 1`, `i ≠ idx + 1` gives `i = idx`, and the
    poison mark rules out a cache at it), and the new one is `thinV_refl` (`:660-674`).
- **The batch lock's quarter stays exact this round.** That is an internal sequencing choice, and
  it keeps every proof `sorry`-free. Its consequence (`ReadSide.lean:575-578`: `L = vData P (C, R)`
  by agreement) is stated where it is used.

### Findings

**R4-2 (hard rule "complete", for group 2; and "after a change, drop what existed only for it").
The clients'-view branch and two commit lemmas still say "the logical view is the physical one".**

*The evidence:*
- **`Unlock.specC`'s second branch** (`Spec/.../batchTxBuffered__Unlock.lean`, `specC`) returns
  `bView γ 1 (sData P st.S)`: the writer's contents, i.e. the physical view.
- **`rtRes_wb_close`** moves all three shares to `vData P (C, writebackR W R)` (`ReadSide.lean`,
  the `view_upd3` and `viewQ_exact` lines).
- **The window case of `rtRes_cm_close`** does the same at `(C', R.reset)` (`:675-677`).
- **The plan.** Section 3.2 has `relog P st.S L` there: the session's writes over `L`, with the
  compacted SB entries kept. mvcc's `bkView γB q m := ∃ vd, bView γB q vd ∗ ⌜keyView vd m⌝`
  (`InvStore.lean:1403`) reads `m` as the logical bucket.

*Why it matters.* On a compacting backend the first put session after a compaction gives the
clients `sData`, which lacks the compacted revisions, while mvcc's `m` still has them. Its
`keyView vd m` is then unprovable, and the apply thread's `Unlock` breaks.

*Callers affected:* every user of `Unlock.spec`'s second branch, 9 files. With `dlNoDel` it
becomes an instance: `relog = sData` when nothing deletable is registered, one law.

*Restatement for the fold:* branch 2 is
`∃ L, bView γ 1 L ∗ Pk ∗ (bView γ 1 (relog P st.S L) -∗ W ∗ Q)`. In the same step:
- `rtRes_wb_close`'s and the window case's new `L` become `relog …`;
- the new physical view is thin of it;
- `relog_noDel : dlNoDel γ ∗ … ⊢ ⌜relog P S L = sData P S⌝` (or its pure form under the thin
  relation) lets the D22 callers keep their exact text.

**R4-3 (preference "after a change, drop what existed only for it"; forward). `thinV_rebase`'s
hypothesis `h2` is not needed.**

`vData_rebase_or` (`ReadLemmas.lean:130-147`) proves: at each key, `(C', X)` reads as `(C, X)` or
as `(C, R)`, given `h2 : vData P (C', R.reset) = vData P (C, R)`. Without `h2` the same case split
gives "as `(C, X)` or as `(C', R.reset)`":
- if `X` has the key, both `(C', X)` and `(C, X)` take `X`'s last value (`ovB`, `Model2.lean:83`);
- otherwise `(C', X)` reads `dget C'`, which is `vOf (C', R.reset)` (`vOf_reset`,
  `ReadLemmas.lean:97`).

So the general lemma, which I checked by reading the definitions but not in Lean, is:
```
thinV γ (vData P (C, X)) L ∗ thinV γ (vData P (C', R.reset)) L ⊢ thinV γ (vData P (C', X)) L
```
It is what group 2's deleting commit needs for the cached states: the view changes there, so `h2`
fails. The no-window case then uses it with the new state's thinness, which it already holds via
`hview`. Restate it now and the commit path's third case needs no new rebase lemma.

## Target 2: O1's fallback (`BNames.dlb`, `dlReg`/`dlNoDel`, `thinV_exact`, the supply points)

### What is good

- **Sound and later-free.**
  - `dlInit` holds the flag's whole fraction at `false`.
  - `dlReg_fix` makes it `true` and discards it; `dlNoDel_fix` discards it at `false`
    (`DelKeys.lean:46-72`).
  - The two persistent outcomes disagree on a discrete value (`dlNoDel_noDel`, `:86-92`), so
    `thinV_exact` needs no `▷`/`◇`. That fixes exactly round 3's uncertainty: `dlReg_false_noDel`
    gave only `▷ False`.
- **Exclusivity is not a loss.** No reader of a compacting backend needs exactness:
  - The view has only `Key` (`bridgeParams`).
  - mvcc's readers consume `snapThin m m' Del` (`InvStore.lean:613`), which is thin by design.
  - `Meta` and `Lease` reads go through the hook's keys and `rbOwn`, outside `vData`.
  - The exact readers (D22's clean read, restore, snapshot send) are excluded on a compacting
    server by M2's premise (no snapshot with the compactor on, `backend-cmp-plan.md` §1, "Out").
- **The supply points are proof edits.**
  - `NewServer.spec` is textually unchanged; only `NewServer.wp_proofM` changed
    (`NewServer.lean:508-511`).
  - `SnapApplyWalk` fixes its new backend's flag (`:283-286`): a D22 proof only, with no D22
    statement changed.
- **The new bridge (`isKeyBackendG_of_backendC`, `BackendBridge.lean:2224-2290`) takes no
  registration premise.** That is right: `bkDel γ` carries `dlIs` itself, so the general bridge is
  mode-free.

### Findings

**R4-1 (hard rule "one spec per function", forward; "Who decides": top-level statements and
reversing a decision are the user's). `dlNoDel` writes the compactor-off mode into top-level
statements.**

*Where it is.* `backend.dlNoDel d.γB` is now a precondition of:
- `mvcc.NewStore_backend` (`StoreBackend.lean:88-89`) and its linked `mvcc_NewStore_backend`
  (`mvcc/Results.lean:263-264`);
- `server_kv_watchable_of` (`BuildLemmas.lean:69-70`);
- `server_kv_backend`, `server_kv_watchable` and `server_kv_backend_hooks`
  (`etcdserver/Results.lean:822, 890, 1041`);
- mvcc's exported `mvcc_backend_bridge` and `mvcc_storeBackend_of_backend`.

`NewServer.wp_proofM` fixes the flag at `false` unconditionally (`NewServer.lean:510-511`).

*Why it is a problem.*
- **Mode baked in.** The flag is fixed once, so a backend under these statements can never
  compact. M2's `NewServer.specCompact` (`NewServer.lean:1975-1983`, a `sorry`) is the
  compactor-on server. Its proof will need `NewStore_backend` and the `server_kv_*` lemmas over a
  backend whose flag is `true`. Either these statements change again, or a compactor-on copy
  appears beside them: the family the hard rule forbids.
- **The user's F6/F7 route.** "After Review round 1" (`backend-cmp-plan.md:349, 357`) chose
  "`dlNone` dropped … the unfixed registration (`dlInit`) … D22's exact readers use that" and
  "F7 (`dlInit` kept unfixed for mvcc)". Fixing the flag `false` replaces that route. The reason
  is real: the old bridge is persistent, so an exclusive `dlInit` cannot serve it. But this is a
  reversal of a user decision, and the plan records it as "decided by the agent while the user
  was away".
- **Who decides.** "Who decides" (`notes/spec-first-plan.md:199-205, 216-219`) lists top-level
  statements and reversals among the user's. Its escalation trigger says such a change "stops
  and goes to the user". The plan lists the statement changes "for the user to review on
  return", which is good, but presents them as taken.

*Restatement.* Let `mvcc.NewStore_backend` and the `server_kv_*` lemmas take
`backend.dlInit d.γB` (the creator's right, exclusive and unfixed), and fix it inside, where the
store's compaction mode is decided:
- `dlNoDel_fix` where the store's compaction authority is frozen (`crevFrozen_alloc`);
- `dlReg_fix γB (keyName-and-delKey γ)` where the store compacts.

The flag stays: it is the right persistent form for the old bridge. Only its *fixing* moves below
the mode-free statements. `bootBackend_of_newPost` already returns `dlInit`, so `NewServer` then
just passes it on. Put both options to the user in this round's batch (keep `dlNoDel` in the
statements until M2, or `dlInit` now), and change the plan's heading to "pending the user".

**R4-6 (preference "the vocabulary is part of the spec"; minor).** `backend.dlNoDel d.γB` sits
next to `mvcc.bkNoCmp d.γB` in the same preconditions, and both comments read "the backend never
compacts" (`StoreBackend.lean:88`). They are different facts:
- `bkNoCmp` is about the data's past: no compaction keys in `Meta` (`InvStore.lean:455-467`).
- `dlNoDel` is about the future: no registered deletion.

*Restatement:* comment `dlNoDel` as "nothing registered deletable: the readers' views are exact".
If R4-1's `dlInit` is taken, the issue disappears.

## Target 3: `safeSt` in place, the put premises, `sessWf_C_in_S`

### What is good

- **The premise "above the committed keys" is what the code needs.**
  - `baseReadTx.UnsafeRange` returns bbolt's keys (from the interval's read transaction, i.e. the
    committed data `C`) followed by the buffer's (`read_tx.go:89, 120-121`). A safe-range result
    is ordered only if every buffered key is above every committed key.
  - The buffer is emptied at every commit (`batch_tx.go:397`), so that `C` is the `C` at the time
    of each buffered put.
  - Keys buffered by the same session need no order: `UnsafeSeqPut` keeps its own `verify`
    premise on `st.W`, and `UnsafePut`'s buffer is deduplicated and sorted at write-back
    (`tx_buffer.go:101-110`).
  - The old premise, "above the writer's contents", demanded more: above the uncommitted puts
    too. The new spec is stronger for its callers. Choosing `C` alone over `specC`'s `S ∨ C` is
    "no unneeded premise", and the agent was entitled to it.
- **`sessWf_C_in_S` is true of Go**, and its hypothesis is the right one. Deletes are never
  buffered (`batch_tx.go:418-421`), and `pendingDeleteOperations`, the model's `ndel`, counts
  every delete since the last commit and is reset only by `unsafeCommit` (`:401`). With
  `ndel = 0`, the writer's contents are `C` plus puts, so every committed key off the hook's
  buckets is in them.
  - **"What when deletes are buffered?"** They never are.
  - **"What after a delete?"** The lemma does not apply, and nothing needs it: in Go, no Key put
    follows a delete in one session. The lessor's `Revoke` deletes the `Lease` record after its
    tombstones (`lease/lessor.go:350, 359`), and compaction puts only `Meta`.
  - Every session starts at `ndel = 0`, because an `Unlock` with a pending delete commits
    (`batch_tx.go:355`).
- **`UnsafePut.spec`'s change is only restated at its callers.**
  - Its two premise-discharging callers put into `Meta`, which is not safe-range, so the premise
    is vacuous: `CindexBackend.lean:259-260, 324-325` and `BackendHooks__OnPreCommitUnsafe`.
  - The D22 callers (`SnapApplyWalk`, `applySnapshot`, `SnapSendBranch`, `BuildLemmas`) only
    pass the spec along. They were not edited and still compile.
- **One twin fewer.** `UnsafeSeqPut.specC` and `safeStC` are gone (hard rule satisfied for that
  function).

### Findings

None.

## Target 4: the remaining variants, the second bridge, group 2's plan

**What remains.** `Unlock.specC`, `UnsafeDelete.specC`, and `isKeyBackendG_of_backendC` (5
`sorry`s) beside the old bridge. All are still unused (`grep`: no caller outside their own
files).

**Group 2's plan (the batch lock's quarter onto `L`) is right in direction.** Three things to add
to it.

1. **R4-2** above: `specC`'s branch 2 to `relog`, together with the write-back and the window
   case.
2. **`batchLocked` must carry `L`.** `specC`'s branch 1 says
   `thinV γ (sData P st.S) (vData P (st.C, st.R))`, i.e. against the *physical* view at lock
   time. Once the batch quarter is at `L`, it must be `thinV γ (sData P st.S) L` with the
   batch's `L`, and `BSess`/`batchLocked` have no `L` today. The plan says "threading `L` through
   `Unlock`/`unsafeCommit`/`commit` is that fold's design". Also list `sessWf`'s agreement clause
   (`ndel = 0 →` the writer's contents agree with the physical view off `HB`, the clause
   `sessWf_C_in_S` uses). It can stay physical, since every session starts after a commit with
   `ndel = 0`, but it must be decided, not inherited.
3. **R4-4 (the hard rule's "special cases are instances"; plan fix). The old bridge's fold is
   by monotonicity, not `congrDel`.**
   - The plan (and round 3) had the old bridge as the new one's instance "through
     `isKeyBackendG_congrDel` and a fixed registration (at `False`)". With the flag, a
     `dlNoDel` backend has no `dlReg`, and `bkDel γ k ∗-∗ Del k` fails for an arbitrary `Del`.
     So `congrDel` cannot give the old bridge.
   - It does not need to. In `isKeyBackendG` (`InvStore.lean:1295-1328`) and `batchTxSpecG`
     (`:1091-1162`), `Del` occurs *negatively* only under `⌜Cmp⌝` (the compacting delete's
     premise, `:1147`). `SR`/`SRh` occur only under `⌜Cmp⌝` (`:1322-1326`). Everywhere else
     `Del` is positive: `snapThin`'s second clause (`:613-615`) and the point read's `Del k`
     disjunct (`:1122`).
   - So:
     ```
     isKeyBackendG_mono : ¬ Cmp' → □ (∀ k, Del k -∗ Del' k) →
       isKeyBackendG … Del … Cmp … SR SRh ⊢ isKeyBackendG … Del' … Cmp' …
     ```
     holds. The old bridge is then the new bridge plus `dlNoDel` (`bkDel γ k ⊢ False ⊢ Del k`,
     by `dlNoDel_noDel`).
   - This also removes the old bridge's own exact proofs of the read clauses (`bridge_crt`,
     `bridge_rt`, `bridge_rt_clean` over `thinV_exact`). Once the new bridge's thin read cases
     are proved, those would otherwise be a second proof of the same clauses. `congrDel` is still
     needed in the other direction, for the store's `Del := delKey γ` (under `◇`, as planned).

**Who decides, for the variants.** Keeping `Unlock.specC`/`UnsafeDelete.specC` until group 2 is
the "parallel family" round 3 asked to put to the user. The plan now has an explicit fold list,
and group 2 is planned to fold both. That answers it, provided group 2's exit criterion is
"every `…C` statement deleted".

## Process: the agent's decisions this round

| Item | Verdict |
|---|---|
| `safeSt`'s clause dropped; the put premise "above C" alone | The agent's (an internal predicate; a weaker premise, i.e. a stronger spec). Fine. |
| The batch quarter exact this round | The agent's (sequencing, no statement). Fine. |
| `rtHeld_view` returns its resources | The agent's (an internal law). Fine. |
| `ConcurrentReadTx.spec`'s post thin | Within the user-approved design (plan 3.2: "readers then get `thinV`"). Fine; list it in the batch as done. |
| The flag `dlb` beside the saved predicate (not O1's "pure key set") | The predicate's design is the agent's, but it **replaces F6/F7's "`dlInit` kept unfixed"**, a user decision. It is the user's to confirm. |
| `dlNoDel` in `mvcc_NewStore_backend`, `mvcc_backend_bridge`, `mvcc_storeBackend_of_backend`, `server_kv_*`; `dlInit` in `bootBackend_of_newPost`'s post | **The user's** (top-level statements; the escalation trigger). Recorded "for the user to review", but presented as decided. See R4-1 for the option that avoids the mode. |
| Editing D22's `SnapApplyWalk` (a proof only) | Fine on substance. Tell the D22 owner: the snapshot track is the collaborator's. |

**R4-5 (documentation; stale text).**
- `DelKeys.lean`'s module docstring ends "The invariants' use of `thinV` (`rtRest`,
  `batchGhostAt`, `cacheValid`) is the stage's next Draft step". `rtRest` and `cacheValid` now use
  it; only `batchGhostAt` is left.
- `Unlock.specC`'s docstring still says "Replaces `spec` once proved (`cacheValidC`, …)", but
  `cacheValidC` is gone.
- `notes/STATUS.md` on this branch (its header) still tells the D22 track that exactness comes
  "through a new exclusive token `dlNone`". F6 dropped that token, and this round replaced its
  successor. `STATUS.md` was not updated in `ddeadfe227..f18481f78a`.

## Ranking (most need of revision first)

1. **The `dlNoDel` statements** (R4-1, R4-6): a compactor-off mode in top-level statements, a
   reversal of F6/F7, presented as decided. They need the user's decision before M2 builds on
   them. The cheap alternative (`dlInit` in the statements, fixed below) keeps them mode-free.
2. **Group 2's plan** (R4-2, R4-4, and `L` in `batchLocked`): `specC`'s branch 2 and the two
   commit lemmas still equate the logical and physical views. The old bridge's fold needs
   monotonicity, not `congrDel`. These are plan fixes now and statement changes at the fold.
3. **The readers' commit lemmas** (R4-3): `thinV_rebase` is more specific than needed. Generalise
   it before group 2.
4. **Docs** (R4-5).
5. **`safeSt`, the put premises, `sessWf_C_in_S`, `thinV`/`viewQ`/`cacheValid`/`ConcurrentReadTx.spec`
   themselves:** right as they are.

## Bugs in the Go code

None found this round. The Go facts used above are etcd's documented behaviour:
- deletes are unbuffered and force a commit;
- the commit's `reset` does not bump `bufVersion`.

Nothing for `issues/`.

## Verified vs uncertain

**Verified** (Go or Lean read):
- **ConcurrentReadTx's cache.** It copies the buffer under `readTx.RLock`, copies deep, and
  reuses the cache only at equal `bufVersion`. The write-back bumps `bufVersion`; the commit's
  reset does not.
- **Deletes.** They are unbuffered, counted in `pendingDeleteOperations`, and that count is reset
  only by `unsafeCommit`. `Unlock` commits when it is positive.
- **Range ordering.** The safe-range reader returns bbolt's keys before the buffer's, so "above C"
  is what ordering needs.
- **Only `Key` is in the view** under `bridgeParams`.
- **The thinness argument.** A reader's state misses only compaction-deleted keys, and the extra
  keys of a stale cache are compacted keys with unchanged values. This rests on Go facts
  (revisions never re-put, deletes unbuffered, the version rule) and on reading the model.
- **The flag's laws.** `dlReg_fix`, `dlNoDel_fix`, `dlNoDel_noDel` and `thinV_exact` hold as
  stated, with no later.
- **Supply points and callers.**
  - The supply points are proof-only in `NewServer` and `SnapApplyWalk`.
  - `NewServer.spec` is unchanged.
  - The listed results gain `dlNoDel`.
  - `NewServer.specCompact` exists and is a `sorry`.
  - `UnsafePut.spec`'s discharging callers put only into `Meta`.
- **`rtRes_cm_close`'s two cases**, as described.
- **The bridges.** The new bridge takes no registration premise, and its five `sorry`s are local.
- **`isKeyBackendG`'s polarity.** `Del` is negative and `SR`/`SRh` occur only under `⌜Cmp⌝`.
- **The build.** Every changed module's `.olean` is newer than its source.

**Uncertain:**
- That no `sorry` of the stage reaches a linked result. I did not run `etc/tcb-report.py --check`.
- R4-3's generalised `thinV_rebase`, checked by reading `ovB`/`vOf_reset`, not in Lean.
- R4-4's `isKeyBackendG_mono`, argued from polarity, not proved. In particular, I did not check
  every definition `isBatchTxG` unfolds to, beyond `batchTxSpecG`.
- Whether any unmodelled reader of the `Key` bucket on a compacting server needs exactness. mvcc's
  `HashByRev` and the corruption checker read `Key` with `UnsafeForEach`. They are outside the
  stage (plan §1) and not checked here.
- Whether `sessWf`'s agreement clause can stay physical once the batch quarter is at `L` (R4-2's
  third point). That is group 2's design.
