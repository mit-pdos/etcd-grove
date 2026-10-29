# backend-cmp, Review round 10 (2026-10-29): question 4, the compaction keys' values

**Under review.** Commit `facf2ad1e1` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`),
diffed against `1ac48a4754`. `0a0f48885e` (before it) and `595f4eaae2` (after it, `HEAD`) change
notes only, so nothing here is stale at `HEAD`. This round judges the implemented statements, not
the plan's text.

**Read.**
- The diff (25 files).
- `InvBackend.lean`: `BNames.fkv` (`:116`), `fkV`, `fkCl`, `fkHalf` and `fkRd` (`:303-321`).
- `Model2.lean`: `BParams.FV` (`:65`), `fkWfD`/`fkWfB`/`fkWfRv`/`fkWfSt`/`fkOk`/`fkOkRv`/`fkWInit`
  (`:436-462`), `hookStep` (`:350`).
- `FkLemmas.lean`: statements only.
- `InvBatch.lean`: `fkHalf_mono`/`_rd`/`_raise`/`_put` and `batchGhost_step*`.
- `NewAlloc.lean`: `backend_init`'s allocation.
- `ReadLemmas.lean`: `fkRd_abs`, `fkRd_wf` (`:985`), `rtHeld_fkRd` (`:968`).
- `Image.lean`: `bkNoCmp_of_fkCl` (`:65`), `fkV_of_fkCl` (`:74`).
- `InvStore.lean`: `metaRevVal` (`:98`), `KBReal.P` (`:105-111`), `kbMW` (`:480-503`), `metaReadTx`
  (`:667`), and the docstrings of `batchTxSpecG` and `isKeyBackendG` (`:1137-1142`, `:1358-1364`).
- `BackendBridge.lean`: `rt_metaWf`, `bt_metaPut` (`:2302`), and `isKeyBackendG_of_backendC`
  (`:2705-2872`).
- `isKeyBackendG_cmp` (`InvStore.lean:2335`).
- `store__checkPrevCompactionCompleted` (its spec and proof).
- The specs `UnsafePut`, `batchTx.UnsafePut`, `OpenBackend` (and its axiom's docstring),
  `MustUnsafeSaveConfStateToBackend` and `MustSaveMemberToBackend`.
- `hooksSpec`/`hookFnSpec` (`InvBackend.lean:733-749`).
- The four `UnsafePut` callers.
- The plan's "Question 4's statements" and "Question 2: recorded".
- Go at the pin:
  - `mvcc/store.go:22-60`;
  - `mvcc/kvstore.go:225-232` (`checkPrevCompactionCompleted`);
  - `mvcc/revision.go:54-117` (`RevToBytes`, `BytesToBucketKey`);
  - a grep of `server/` for the two key names: only `store.go:47,59` write them.

**Build.** I did not build. When I read the log of record (`be-q4-build.log`), it was at
`[10933/10943]` with no `error`/`✖` line. `FkLemmas`, `ReadLemmas`, `NewAlloc` and `BackendBridge`
were already built or replayed without errors. Check the log's last line before relying on it.

## Summary

- **No Tier-1 finding.**
  - The well-formedness bit is sound. Every route that changes a batch state keeps `fkOk`: puts,
    `SeqPut`, deletes, bucket creation and deletion, write-back, commit, `setHw`, and the hook
    (through `batchLocked`). The only route that can write a compaction key now needs a well-formed
    value.
  - `OpenBackend` claims nothing new about the file.
  - `fkRd_wf` is sound under concurrent puts.
  - The new `RLock`/`RUnlock` token is right: it is a reader slot the code takes.
- **The two agent decisions are good:**
  - a persistent bit beside the `monoNat` flag, rather than a third level of the flag;
  - `BParams.FV`, rather than a backend copy of mvcc's encoding.
- **Five Tier-2 items:**
  - R10-1: a missing law. Each of `fkCl`'s two laws consumes it, so the wiring step cannot get both
    `bkNoCmp` and `fkV γ true` from one `fkCl`.
  - R10-2: stale and missing docs.
  - R10-3: the trust-base record for the axioms whose meaning grew.
  - R10-4: the margin and the restart case.
  - R10-5: the dead `viOk` and the design sketch of `BParams.VI`.
- **R9-1 is done** except the trust-base list. **R9-2 is done.** R9-3 stays deferred, as planned.
- **Stop rule:** this is the first round of the question-4 increment and it has no first-tier
  finding, so there is no churn. Close the increment's review.
- **No Go bug.**

## What is good

### The bit is sound: no route can break `w = true`

- **What the bit says.** `fkHalf` now holds `∃ f w, monoNatAuthOwn γ.fk ½ f ∗ fkV γ w ∗ ⌜fkOk P f w
  st⌝` (`InvBackend.lean:315`). `fkV` is a discarded `dghostVar` (`:303`), so `w` agrees with the
  one allocated at creation and can never change. So `w = true` means every batch state the lock
  invariant ever holds satisfies `fkWfSt`: committed data, read buffer, session data and write
  buffer.
- **I checked every way the state moves:**
  - **`UnsafePut`:**
    - at a compaction key it goes through `fkHalf_raise`, and its `hR` is `fkOk_putFk`, which
      needs `P.FV vb` (the spec's new premise);
    - elsewhere it uses `fkOk_put` (`batchTxBuffered__UnsafePut.lean:57-58`).
  - **`UnsafeSeqPut`:** it takes `¬ fkKey` (`Hfk`), so it uses `fkOk_put`.
  - **Deletes and buckets:** `fkOk_del`, `fkOk_create` and `fkOk_delBucket`.
  - **Write-back** (`Unlock`): `fkOk_wb`, then `fkHalf_rd` for the readers' new state.
  - **Commit and `setHw`:** `fkOk_commit` (all three branches of `unsafeCommit`) and `fkOk_setHw`.
  - **The pre-commit hook** returns `∃ st', batchLocked γ P b st'` (`hooksSpec`, `:740`). That
    bundles `fkHalf` at `st'`, so a hook can change the state only through the operations above.
    Its puts go through `UnsafePut`'s spec with the new premise (`OnPreCommitUnsafe.lean:82`,
    `CindexBackend.lean:267,333`).
  - **The inner `batchTx.UnsafePut`** acts on `btW` and has no ghost. Only `batchTxBuffered`
    advances `batchGhost`, and that is the route clients have (Go's `BatchTx()` returns the
    buffered transaction).
  - **Snapshot images** (`OpenSnapshotBackend`) get fresh names and a bit computed from their own
    `D`.
  - **Defragmentation** is not specified. Go's `defrag` copies values verbatim, so a future spec
    would keep `fkWfD`. *Uncertain: not checked against a spec, since none exists.*
- **The proofs are mechanical.** None of the new lemmas uses `sorry`, `axiom` or `opaque`.
- **"Any client may put any value" is now excluded only where the backend promises something.**
  The new premise `fkKey bi.name kb → P.FV vb` binds only a creator that chose a restrictive `FV`.
  - Under the default `FV := True` it is free.
  - Under `KBReal.P` (`FV := metaRevVal`) the only Go writers are `UnsafeSet{Scheduled,Finished}
    Compact` (`store.go:47,59`). They write `RevToBytes(Revision{Main: rev})` with
    `rev ≥ 0`: `updateCompactRev` rejects `rev ≤ compactMainRev`, and `compactMainRev ≥ -1`.
  - The premise is not an unneeded one. The reader needs it: Go's `BytesToBucketKey`
    (`revision.go:98-109`) panics on a wrong length, a wrong separator or a negative main. That is
    also why `metaRevVal` has `0 ≤ sint.Z x`.

### `fkWInit P D` is computed right, and `OpenBackend` claims nothing new of the file

- **The computation.** `fkWInit P D := decide (fkWfD P D)` (`Model2.lean:461`). `fkOk_init` covers
  the initial state `st0 D wtx` (`C = S = D`, empty buffers). `backend_init` allocates the bit at
  that value and discards it immediately (`NewAlloc.lean:497-498`). So the bit is a fact about `D`
  plus the maintenance above. Nothing is assumed about which values `D` holds.
- **No new claim about the file.** `OpenBackend`'s axiom is justified by "its post is `New`'s proved
  post" (the axiom's docstring, `OpenBackend.lean:26-40`). The new conjunct `fkV γ (fkWInit P D)`
  comes from that same proof. For an arbitrary file it says only "true iff the file's compaction
  values satisfy `P.FV`". Since `P` is the caller's, this is a decision about `D`, not a claim about
  Go. The axiom says nothing new about the file or about Go.

### `fkRd_wf` under concurrency

- `fkRd γ P rv` is bound to one reader state `rv`.
- A reader state is published only under the batch lock, by write-back or commit. At that moment
  `fkHalf_rd` turns the lock's `fkOk P f w st` into `fkOkRv P f w rv`, with the same persistent
  `fkV γ w`.
- Concurrent puts change `st.S`/`st.W` but not a published `rv`. With `w = true`, those puts can
  only add well-formed values anyway.
- `fkRd_wf` (`ReadLemmas.lean:985`) uses only `dghostVar_agree` on the discarded bit. It holds for
  any interleaving.

### The two agent decisions

- **A persistent bit, not a third level of the flag: right.** A `monoNat` gives readers only lower
  bounds. "Well formed" would need an upper bound (`f ≤ 1`), which only the holder of the client's
  exclusive half knows. `checkPrevCompactionCompleted` runs concurrently with the job that holds
  that half, so it could not learn it.
  - The bit is readable by anyone, and it is stable, because the only way to write a compaction key
    needs a well-formed value.
  - Its margin is in R10-4.
- **`BParams.FV`, not a backend copy of `revBytes`: right.**
  - A copy would make the backend state mvcc's encoding: coupling, and a spec of an implementation
    detail of another package.
  - `FV` is a creator-chosen parameter in the same family as `HK`, `RB` and `SB`. With the default
    `True`, no other creator or use changes.
  - It is a predicate parameter of a library predicate (the TaDa/HoCAP preference). But it is fixed
    at creation and read through one law (`fkRd_wf`), so the cost the principle warns of ("changes
    every use when it changes") does not arise.
  - A real-backend wiring that forgot to set it fails at the bridge's `hFV`, not silently.

### `metaReadTx rt RT`: the token is one the code needs

- Go's `checkPrevCompactionCompleted` takes `s.b.ReadTx()` and calls `RLock`/`RUnlock`
  (`kvstore.go:226-228`), which uses a slot of the read transaction's `RWMutex`.
- The old `{{ True }} RLock` could not be met by the real backend: an exclusive resource needs a
  token. Taking the contract's own reader budget `RT` and handing it back from `RUnlock` mirrors
  `keyReadSnap`.
- Over mvcc's assumed backend `RT = True` (`isKeyBackendG_cmp`), so the proof of
  `checkPrevCompactionCompleted` is unchanged.
- In the C bridge's proof, the token is `bkRTx`, split into `rdOpen` and back (`:2836-2871`).

### The new bridge's `metaReadTx` case

- `rt_metaWf` is sound and complete for `metaReadSpec`:
  - when the key is absent, both output slices are empty;
  - when it is present, the value satisfies `metaRevVal`, through
    `hFV v (fkWfRv_vOf Hwfv hP.2.1 (fkKey_meta Hkn) hvo)`.
- `isKeyBackendG_of_backendC` now has one `sorry`, the limited range (`:2785`, question 2's). The
  `MW` step-put obligation that round 9 counted at `:2701` sits inside it.
- `hFV : ∀ v, P.FV v ↔ metaRevVal v` uses both directions: `→` for the read, `←` for `bt_metaPut`.
  `KBReal.P` meets it by `Iff.rfl`.

### The four `UnsafePut` callers

- `hookTM_put_ci`, `hookTM_put_term` (`CindexBackend.lean:267,333`) and `OnPreCommitUnsafe`'s
  confState put (`:82`) put keys that are not compaction keys. Each discharges the premise with
  `fun h => absurd h (by decide)`, one argument.
- `bt_metaPut` (`BackendBridge.lean:2350`) gets `metaRevVal v` from `metaPutCap`'s premise (`hv`)
  and passes `fun _ => hFV v hv`.
- No other caller of `batchTxBuffered.UnsafePut.spec` puts directly:
  - `BuildLemmas`, `SnapApplyWalk`, `SnapSendBranch` and `applySnapshot` only pass `hPut` on to
    these lemmas;
  - the lease and membership axioms take the caller's own triple and write other buckets.

## Findings

### R10-1 (Tier 2, law coverage; affects the wiring step). Each of `fkCl`'s laws consumes it

- **Evidence.**
  - `bkNoCmp_of_fkCl : fkCl γ P D ⊢ bkNoCmp γ` (`Image.lean:65`) and
    `fkV_of_fkCl : fkCl γ P D ⊢ fkV γ true` (`:74`) each take the whole `fkCl`.
  - Today's callers use only the first: `BootBackend.lean:93` and `SnapApplyWalk.lean:394`.
  - The plan says the wiring step "supplies `fkV γ true` from `fkV_of_fkCl`". At that step it
    also needs `bkNoCmp`, which `store.restore` consumes.
  - With these two laws, a client can get both only by unfolding `fkCl` (principle: "a client does
    not unfold … each unfold is a missing law").
- **Also missing: a backend-level law for a file that has compaction keys.**
  `fkInit_wf` (`FkLemmas.lean:354`) goes the other way. A restart over a file that records a
  compaction will need the bit from `fkWfD P D`.
- **Restatement.**
  - `fkCl_noCmp (h : noCmpData D) : fkCl γ P D ⊢ bkNoCmp γ ∗ fkV γ true` (keep the two laws as
    corollaries, or drop them);
  - in the backend, `fkCl_wf (h : fkWfD P D) : fkCl γ P D ⊢ fkCl γ P D ∗ fkV γ true`.

### R10-2 (Tier 2, docs). Stale names and new hypotheses not in docstrings

- `Spec/.../storage/OpenBackend.lean:17` and `OpenSnapshotBackend.lean:13` still name
  `mvcc.bkNoCmp_of_fkOwn`, which is gone. They say `newPostK` holds "the client's half of the
  compaction keys' flag" and omit the bit.
  - **Restatement:** "the client's half of the compaction keys' flag and the bit of their values
    (`fkCl`: `bkNoCmp_of_fkCl`, `fkV_of_fkCl`)".
- `isKeyBackendG_of_backendC`'s docstring (`BackendBridge.lean:2705-2712`) does not mention its two
  new hypotheses.
  - **Restatement:** add "over a backend whose compaction values are mvcc's (`hFV`) and well formed
    (`fkV γ true`, from `fkV_of_fkCl` at creation)".
- `isKeyBackendG`'s docstring (`InvStore.lean:1358-1364`) does not say that `metaReadTx`'s `RLock`
  takes `RT`.
  - **Restatement:** add "under the reader's budget `RT`, given back by `RUnlock`".

### R10-3 (Tier 2, trust base). Record that the axioms whose meaning grew stay true

- **`OpenBackend`'s meaning grew** (`newPostK` gains `fkV`), and so did that of every axiom whose
  statement carries `isBackend`/`batchLocked`, because `fkHalf` now carries `fkOk`:
  - `backend.Snapshot`;
  - `MustSaveMemberToBackend` (over `d.γB`).
- **Each stays true:**
  - `OpenBackend`'s new conjunct is `New`'s proved post (above).
  - `Snapshot` only commits (`fkOk_commit`).
  - `MustSaveMemberToBackend` puts into `members`, which is not an `fkKey`, so `fkOk_put` applies
    and no `FV` premise arises.
- **But the record is not updated.** The plan's trust-base list (`backend-cmp-plan.md:960-967`)
  still says "a commit keeps `fkAbsSt`".
- **Under the plan's axiom rule**, `OpenBackend` is an axiom-backed spec whose meaning changed.
  - I do not think it needs another `axiom` skill run: the change is ghost-only and comes from
    `New`'s proof.
  - Say so in one line in `notes/axiom-review/openbackend.md`, so that the freeze check sees it was
    considered.
  - R9-1's trust-base part (`MustUnsafeSaveConfStateToBackend`) is still only a to-do
    (`:996`). Apply it to the list at the same time.

### R10-4 (Tier 2, know the margin). What the bit does not cover

- **The bit is fixed at creation.** A backend opened over a file with one malformed compaction value
  keeps `w = false` forever, even after the store overwrites both keys.
  - Go's restore would already have panicked on such a file (`BytesToBucketKey`), so nothing real
    is lost.
- **`metaRevVal` excludes the marked (18-byte) form**, which `BytesToBucketKey` accepts. This is
  conservative: no writer produces it.
- **The restart case.** Booting over a file that records a compaction (today excluded by `bootOk`'s
  `noCmpData`, the user's decision) will need `fkWfD (KBReal.P d) D` of the file as a premise or an
  invariant of the previous run, beside question 5.
- **Restatement:** two sentences in `fkV`'s docstring and in the plan's question-4 entry.

### R10-5 (Tier 2, "drop what existed only for what it changed"). The `VI` design is dead

- `DelKeys.lean:97-101` keeps `viOk`, with a docstring about `BParams.VI` and `metaVI`. Neither
  exists, and nothing uses `viOk`.
- The plan's design sketch still writes the bridge with `metaVI P` and `P.VI`
  (`backend-cmp-plan.md:51-55,150-154,289,304`).
- **Restatement:**
  - delete `viOk`, or have it ride with the next `DelKeys` change;
  - mark those plan lines as superseded by "Question 4's statements".

## Round 9's findings at `facf2ad1e1`

- **R9-1: done for the docstrings.** `batchTxSpecG` (`InvStore.lean:1140-1142`) and `isKeyBackendG`
  (`:1361-1364`) now name `MW`. The trust-base list still lacks `MustUnsafeSaveConfStateToBackend`;
  it is recorded only as a to-do (plan `:996`). See R10-3.
- **R9-2: done.** `kbMW`'s docstring states the cost (`:495-498`), and the plan (`:988-993`) says the
  compaction results "must not be counted as verified" until the wiring step. STATUS does not claim
  them.
- **R9-3: deferred**, as planned (wiring step).

## The stop rule (`notes/spec-first-plan.md`, "When to stop iterating")

- **Which increment.** This is the question-4 increment (the statements this commit introduced:
  `fkV`, `fkCl`, `FV`, `UnsafePut`'s premise, `metaReadTx`'s `RT`, the bridge's `hFV`/`fkV`). This
  is its first round.
- **No churn.** There is no first-tier finding, so none comes from this repair or from round 9's.
- **Recommendation.**
  - Close this increment's review.
  - R10-1 is a law to add when the wiring is written. The wiring step is where it would surface.
  - R10-2, R10-3 and R10-5 are docs, which can ride with the next code change.
  - The axiom check before the freeze is satisfied by R10-3's one-line record; no new axiom was
    added.

## Go code

- No bug found, and no `issues/` entry is needed.
- `BytesToBucketKey` panics on a malformed value read from a corrupted database file. That is
  defensive behavior on corrupted input, and no writer produces such a value.

## Ranked by need of revision (two-tier rubric)

There is no Tier-1 finding. Tier 2, in order:

1. **R10-1:** `fkCl`'s laws, `bkNoCmp` and `fkV true` from one `fkCl`, and the backend-level
   `fkCl_wf`.
2. **R10-3:** the trust-base record (`OpenBackend`'s grown post, `fkOk` in the list, ConfState).
3. **R10-2:** stale `bkNoCmp_of_fkOwn` in two spec docstrings; the bridge's and `isKeyBackendG`'s
   docstrings.
4. **R10-4:** the margin and the restart premise, stated in the docs.
5. **R10-5:** the dead `viOk` and the `VI` sketch.

Targets by need of revision:

1. `fkCl`, `bkNoCmp_of_fkCl` and `fkV_of_fkCl`: R10-1.
2. `OpenBackend.spec` and `OpenSnapshotBackend.spec`: R10-2 (docs) and R10-3 (record).
3. `isKeyBackendG_of_backendC` and `isKeyBackendG`: R10-2, docstrings.
4. `fkV`: R10-4, docstring.
5. No change needed:
   - `fkHalf`, `fkRd`, `fkOk` and `fkRd_wf`;
   - `BParams.FV` and `KBReal.P`;
   - `batchTxBuffered.UnsafePut.spec`;
   - `metaReadTx`;
   - `rt_metaWf` and `bt_metaPut`;
   - `newPost`/`newPostK`;
   - the four callers.
