# backend-cmp, Review round 6 (2026-10-29)

**Commit under review.** `9c61edfb8e` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`).
The changes since round 5 are `29378c4423..9c61edfb8e`, three commits:
- `690afb9a10`: the new bridge's two read cases and the slot triples; R5-4; `metaReadTx`'s `sorry`
  narrowed;
- `7c7097a342`: the new bridge's `Meta` put case (`bt_metaPut`, with `UnsafePut.spec` and `hHK`);
  `metaPutCap` takes its slices read-only for good;
- `9c61edfb8e`: the plan's sections on `metaReadTx` and `BParams.VI`, held on the trust base.

Round 5's report is `notes/spec-first-study/backend-review-5.md`.

**Go.** Read at the pin: `/shared/etcd-grove/.lake/go-src/etcd/server/storage/{backend,mvcc,schema}`.

**Build.** `lake build --no-build` on `BackendBridge`, `UnsafeSetFinishedCompact` and
`UnsafeSetScheduledCompact`: "All targets up-to-date". Each changed module's `.olean` is newer than
its source. The bridge has two `sorry`s left (`BackendBridge.lean:2614`, the limited range;
`:2662`, `metaReadTx`), down from five. The new code also brings three deprecation warnings
(`if_true`/`if_false` in `keyView_thin`, `:2390, 2400, 2402`), which are trivial. I did not run
`etc/tcb-report.py`, because it writes `.lake/tcb.json`. The bridge is still linked nowhere
(`grep`), so its `sorry`s reach no result.

## Summary

- **The round's proofs are right, and so is the `metaPutCap` repair.**
  - Go keeps the put's slices: `txWriteBuffer.put` → `bucketBuffer.add` stores the slice headers,
    `tx_buffer.go:50-53, 75-82, 203-211`.
  - Go never writes them afterwards: `rbytes` is a local of `UnsafeSet*Compact`
    (`mvcc/store.go:43-47, 55-59`), and the key is a `schema` global.
  - The repair is within the agent's remit (Target 1).
- **`hHK` is true of `KBReal.P`.** It is needed, not slack.
- **The main finding is about question (2), not about the commits.**
  - **R6-1.** The axiom `mvcc.kbNoCmp_metaNone` is **false as stated today**, whichever option is
    chosen. Its antecedent can be satisfied for any `rt`: take `L := False`. Nothing ties `rt` to the
    backend that `bkNoCmp` is about.
  - It is also persistent beyond the read hold, so M2's compaction would make it false a second way.
  - Option (b) ("keep the axiom") is therefore not available as worded. Option (a) as worded does
    not repair it either: it keeps `L`/`RT` free and does not anchor `rt`.
  - The user's question must be restated before the user sees it.
- **Question (1) (`viewAt`): round 5's assessment stands.** The plan's "held" paragraph still offers
  option (b) in its unsound wording ("leaving `viewAt` as is"). The correction is only in a later
  paragraph.
- **`BParams.VI`'s cost list misses a trust-base consequence (R6-3).** Putting `viOk` into `safeSt`
  makes the axiom `storage.OpenBackend`'s post (`newPostK` → `isBackend`) assert it of an arbitrary
  on-disk `D`, unless `openPre` gains a premise.
- **The plan cites a precedent that does not exist (R6-2).** It cites the cindex's `metaReadTx`
  as "proved over the real backend". It is a premise (`CindexBackend.lean:27-30`), with the same
  token-free `RLock` shape.

## Round 5's findings at `HEAD`

| | Status |
|---|---|
| R5-1 (`relog` falls back to `L` only in safe-range buckets) | **Recorded** in "After Review round 5" (`backend-cmp-plan.md:678-681`). The design paragraph it corrects (`:648-652`) still states the old `relog` and the backwards parenthesis "compacted keys stay out of mvcc's bucket". Not a statement yet, so nothing to fix in Lean. The plan text should be corrected in place (R6-6). |
| R5-2 (`viewAt` options; trust base) | **Recorded** (`:673-678`). The "Held for the user" paragraph (`:661-667`) still states (b) as "a separate view quarter for D22, leaving `viewAt` as is", which is exactly the unsound hazard (R6-6). |
| R5-3 (R4-4's lemma lets `SR`/`SRh` vary) | **Recorded** (`:681-682`). Its second half (instantiate `Del'` with the old bridge's `Del` directly, not `fun _ => False`) is not; `:636-637` still says `fun _ => False`. Minor. |
| R5-4 (dead `vData_rebase`, `vData_rebase_or`) | **Fixed** (`ReadLemmas.lean`; `grep -w` finds no use). The rename of `vData_rebase_or'` to drop the prime was not done. Trivial. |
| R5-5 (`keyCleanRead_of_backend` not exported) | **Recorded** (`:683-684`). `:624` still lists it among the exports. Trivial. |
| R5-6 (two fix sites) | **Recorded** (`:697-698`, the fold list). |

## Target 1: `metaPutCap` read-only for good (`InvStore.lean:1006-1031`), and its two callers

### What is good

**It is true of Go.**
- `batchTxBuffered.UnsafePut` hands the key and value to bbolt's writer and to
  `txWriteBuffer.put`. That stores the slices themselves (`bucketBuffer.add`, `tx_buffer.go:203-205`).
- Every later use only moves `kv` headers: `merge` (`:214-225`), `dedupe` (`:228-241`), `CopyUsed`,
  the write-back. Readers get the same slices back from `bucketBuffer.Range` (`:175-177`).
- So the backend keeps reading those bytes after `UnsafePut` returns. The old form, which lent the
  slices at `{dq}` and gave them back, could not be met by a backend that keeps them. This is the
  same point `batchTxBuffered.UnsafePut.spec` already makes (`key ↦*□ kb ∗ value ↦*□ vb`, "both keep
  the slices"). The cindex's `metaPutSpec` has the same shape (`InvCindex.lean`: `key ↦*□`, value
  consumed).

**The callers can meet it.**
- `UnsafeSetScheduledCompact`/`UnsafeSetFinishedCompact` (`mvcc/store.go:43-59`) allocate `rbytes`,
  fill it, pass it to `UnsafePut` and return. Nothing writes it afterwards.
- The key is `schema.ScheduledCompactKeyName`/`FinishedCompactKeyName`. It is already `↦□`: the old
  instantiation used `DFrac.discard`. Nothing in Go writes those globals.
- The proofs persist `rbytes` with `ownSlice_persist` before the call
  (`UnsafeSetFinishedCompact.lean:54`, `UnsafeSetScheduledCompact.lean:54`). Each change is
  two lines.

**It is within the agent's remit.**
- `metaPutCap` is an internal predicate of mvcc's backend contract. It appears only under `⌜Cmp⌝` in
  `batchTxSpecG` (`InvStore.lean:1154, 1159`) and in the two `UnsafeSet*Compact` specs.
- Those specs' only callers are mvcc's own (`SetScheduledCompact`, the job).
- The change weakens what a provider of the contract must prove: every provider still works. It
  strengthens a precondition only for mvcc-internal callers, both adapted.
- No closed theorem's text changes. The old bridge's exported `isKeyBackendG` has `Cmp` false,
  where the clause is vacuous.
- No family, no trust-base statement.
- It is recorded as "decided by the agent", with the alternative (a copy in the contract, which Go
  does not make). That is the "Who decides" process.
- The unfolded statements of the two `UnsafeSet*Compact` specs change. Round 5 already listed them
  for the user's batch, so the batch entry should mention the slices.

### Findings

None. One note: the docstring in the `InvStore.lean:1015-1019` comment says "review round 6's
finding". It was the agent's own finding, made in round 6's batch, so "the backend-compaction
stage, 2026-10-29" is more accurate. Trivial.

## Target 2: the new bridge's proofs (`BackendBridge.lean`)

### What is good

- **`keyView_thin` (`:2377-2433`)** is the lemma round 5 predicted. The physical `Key` bucket
  `m'` is `m` filtered to the keys the physical view has. `snapThin m m' (bkDel γ)` comes from
  `thinV`'s `Hsub` and its registered-deletes half. No new premise.
- **`bridge_crtC` and `bridge_rtC` (`:2438-2533`)** are the old proofs with `keyView_thin` in
  place of exactness:
  - `bridge_rtC` gets thinness from `rtHeld_view` at the `RLock`;
  - `bridge_crtC` gets it from `ConcurrentReadTx`'s post (the thin post round 1 approved).

  This is independent of R4-2, as round 5 said.
- **The slot triples (`:2645-2659`)** unfold `srSlot`/`srHeld` and apply the backend's
  `LockForSafeRangeDelete`/`UnlockForSafeRangeDelete` specs, taken as hypotheses (`hLSR`, `hUSR`).
  These are the Link pattern.
- **`bt_metaPut` (`:2137-2202`)** is correct, and its docstring's reason for needing no value
  invariant is right. The put is into `Meta`, a hook bucket (`HB`), so
  `sData_insert_HB`/`viewSame_putHB` show that nothing the readers see changes. The value's form
  matters only to a reader of `Meta`.
- **`bt_unlockOAt` (`:2113-2135`)** discharges both `unlockAt` branches through `bt_unlockO`.
- **`hHK` is true.**
  - `KBReal.P`'s `HK` is `n = Meta ∧ (k = "consistent_index" ∨ k = "term")`
    (`InvStore.lean:101-105`; `etcdserver/Base.lean:48, 51`).
  - The compaction keys are `"scheduledCompactRev"`/`"finishedCompactRev"`
    (`schema/bucket.go:82-84`; `InvStore.lean:585-590`). So `hHK` holds by `decide` for every
    `KBReal`.
  - It is needed: a put of a hook's own key needs the client's half (`hkPut`), which mvcc does not
    hold.
  - It is the same kind of premise as `hooksParams`' `P.HK Meta confState = false`
    (`InvHooks.lean:51`).

### Findings

**R6-5 (minor; preference "every premise has a source the client sees").**
- `hHK` is a free hypothesis of `isKeyBackendG_of_backendC`. Every instance is a `KBReal.P`, where it
  is `decide`.
- Either add it as a conjunct of `bridgeParams` (the old bridge's instances then prove it once, by
  `decide`, in `KBReal`'s `bridgeParams` lemma), or state `KBReal.P_hHK` next to `KBReal.P` and use
  it at linking.
- Otherwise the linking file has to prove it inline, and the statement has one more binder.

## Target 3: pending question (1), R4-2/D22's `viewAt` (options a/b)

Nothing in Lean moved since round 5:
- `viewAt γ vd := ghostVar γ.view ¼ vd` (`InvSnapshot.lean:129`);
- the `Snapshot` axiom is unchanged;
- `SnapSendBranch.lean:211` still discards `viewAt`.

Round 5's assessment stands:
- **(a) `viewAt γ vd := ∃ L, ghostVar γ.view ¼ L ∗ thinV γ vd L`: sound.** It only weakens the
  `Snapshot` axiom's premise, and costs D22 nothing today.
- **(b) as worded ("a separate view quarter, leaving `viewAt` as is"): unsound.** All shares of
  `γ.view` agree. If the batch quarter moves onto `L` and `viewAt` is left as is, the `Snapshot`
  axiom becomes false after a compaction (`Q vd := vd = L₀`).
- **(b′) a new ghost name for the physical committed view: sound.** It needs a second update at
  every commit site (`InvCommit.lean`, `NewAlloc.lean`, `ReadSide.lean`'s closes) and a `BNames`
  field.

Both remain trust-base questions as well as D22 questions.

### Findings

**R6-6 (process: "Batching", the question as the user reads it).**
- The plan states question (1) twice:
  - the "Held for the user" paragraph (`backend-cmp-plan.md:661-667`) with the unsound (b);
  - the round-5 paragraph (`:673-678`) with the correction.
- R5-1's `relog` is likewise wrong at `:648-652` and right at `:678-681`.
- When the user reads the batch, the first version they meet is the wrong one.
- Put the round's questions in one place, stated once:
  - (1) a/b′ with the trust-base reason;
  - (2) as restated below, with the `store.Compact.spec` token question;
  - (3) the trust-base part of `BParams.VI` (R6-3).
- Mark the superseded paragraphs as such.

## Target 4: pending question (2), `metaReadSpec` and the axiom `kbNoCmp_metaNone`

The plan's options (`backend-cmp-plan.md:739-748`):
- (a) generalize `metaReadSpec` with a lock token and lent slices, and restate the axiom over it;
- (b) keep both, and give the compaction a token-threaded read under a new name (a second family).

The plan's finding is right:
- the real backend's `readTx.RLock` needs `rdTok ∗ bOpen`, and its `UnsafeRange` needs the held
  lock, lending bbolt's slices;
- `metaReadSpec`'s persistent `vsl ↦*□ v` is false of bbolt's slices, which are valid only while the
  hold lasts;
- `metaReadTx` cannot be met at precondition `True`.

### Findings

**R6-1 (hard rule "sound": a trust-boundary axiom true of the code). The axiom
`mvcc.kbNoCmp_metaNone` (`NoCmpRead.lean:38-41`) is false as stated today.**

Statement:
```
axiom kbNoCmp_metaNone (γ : StoreNames) (RT : IProp GF) (Del : GoString → IProp GF)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    kbNoCmp γ.kb γ.bucket ⊢
      (keyReadSnap (bucketView γ) RT Del true rt m L ∨ keyReadSnapC (bucketViewC γ) RT rt m L) -∗
      □ metaReadSpec rt true
```

*The evidence.*
- **The antecedent is trivial for every `rt`.** `rt`, `RT`, `Del`, `m` and `L` are all free.
  - `keyReadSnap View RT Del rng rt m L` is `□ ∀ q, {{ L ∗ View q m }} rt.RLock() {{ … }}`
    (`InvStore.lean:718-722`), and `keyReadSnapC` has the same shape (`:731-735`).
  - With `L := False`, both hold of any `rt`, whatever its `RLock` does.
- **So, given `bkNoCmp d.γB` for one backend, the axiom yields
  `□ metaReadSpec rt true` for any `rt`.**
  - That is the claim "`rt.UnsafeRange(Meta, compaction key)` returns nothing", at precondition
    `True`.
  - `bkNoCmp` is given by `storage.OpenBackend`'s axiom for a `D` with `noCmpData D`
    (`Spec/.../storage/OpenBackend.lean`, post).
  - Take `rt` to be the `readTx` of a *second* backend opened over a `D₂` whose `Meta` holds
    `finishedCompactRev`. `OpenBackend` accepts any `D`. Go's `baseReadTx.UnsafeRange` then returns
    the key (`backend/read_tx.go:78-89`), and the axiom says it returns none.
  - I did not derive `False` in Lean: the backend's specs do not pin what a read of a hook bucket
    returns, so no other statement contradicts it. But the axiom is false of the code, which is the
    hard rule.
- **Even when `rt` is the right backend's, the axiom is too strong in two ways.**
  1. **It is lock-free.** The triple's precondition has no hold. In Go, `UnsafeRange` without
     `RLock` races with `unsafeCommit`'s write-back and `rt.reset()` (`read_tx.go:133-138`), which
     take `rt.Lock()`. That is a data race on `txReadBuffer.buckets`, a map. Whether Perennial's
     model makes that UB is **uncertain**; Go does not guarantee the result.
  2. **It is persistent beyond the hold.** `restore` applies the axiom before its `RLock`
    (`store__restore.lean:85, 596`), and gets a `□` triple for `rt` forever.
     - `s.b.ReadTx()` returns the same `readTx` for the backend's life.
     - Once M2 compacts over the real backend, `SetFinishedCompact` writes the key.
     - The persistent triple then says a later read finds nothing, when Go finds it.
     - This is the same pattern as R5-2's `Snapshot` hazard: an unchanged trusted statement that
       turning compaction on silently falsifies.

*The callers affected.* `store.restore` (two uses, `store__restore.lean:85, 596`), and through it
every result that reaches `NewStore`/`store.Restore`. The axiom is in the baseline and in nine
collections: `etc/tcb-baseline.txt:570`, `etc/tcb-collections/{mvcc,server,putget,…}.txt`.

*What this means for the options.*
- **(b) "keep `metaReadSpec` and the axiom" is not available as worded.** The axiom must change
  anyway.
- **(a) as worded does not fix it.**
  - "`Tok` and `Rd` from the `keyReadSnap`/`keyReadSnapC` it already takes" keeps `L`, `RT` and
    `rt` free.
  - `keyReadSnap`'s `Tok` is existential inside `RLock`'s post. Naming it from outside means "every
    hold's token", which is persistent beyond the hold again.
  - With `RT := False`, `keyReadLocked`'s `RUnlock` triple has a post nobody uses, so even the
    post-`RLock` form must not leave `RT` free.

*Restatement (for the user's question; a sketch, cost uncertain).* The fact must be:
1. **anchored to the backend `bkNoCmp` is about**, so `rt` cannot be arbitrary;
2. **scoped to one hold**, so it cannot outlive a later compaction.

Two forms do both:
- **(a′) at the backend, where `rt` is anchored.** For instance:
  `bkNoCmp γB ∗ rtHeld γB P b rtx rv ⊢ ⌜no compaction key in rv⌝ ∗ rtHeld γB P b rtx rv`.
  - `rtHeld` contains `bF "readTx" b ↦□ rt` and pins the readers' state `rv`
    (`InvBackend.lean:818-821`), and `rv` covers `Meta` physically.
  - The axiom consumes `bkNoCmp`. `OpenBackend` gives one per open, and `NewStore` consumes it in
    `restore`, before any store over the backend can compact. The pure fact is about that hold's
    `rv` only.
  - mvcc's form is then derived in the bridge from the backend's `readTx.UnsafeRange` spec (if it
    returns `rv`'s contents for a hook bucket: **uncertain**, I did not read that spec's `HB` case).
  - It reaches `restore` as a clause of the contract's `ReadTx`/`RLock` post, for example
    `kbNoCmp kb γb -∗ metaReadSpec' rt Tok Rd true` inside the hold. That is a change to
    `isKeyBackendG`, an mvcc-internal predicate that appears in exported statements (the user's
    batch).
  - The axiom becomes a statement about bbolt data at open, which is what `bkNoCmp`'s docstring
    says it means (`InvStore.lean:455-467`).
- **(a″) the mvcc form, consumed with one hold.** For instance:
  `kbNoCmp γ.kb γ.bucket ∗ Tok ∗ keyReadLocked RT true rt m' Rd Tok ∗ ⌜rt is the store's backend's
  ReadTx⌝ ⊢ …`. The anchoring premise has no source at the mvcc level today, so in practice this
  becomes (a′).

*Cost of (a′)/(a″) against the plan's (a).* The same restatement of `metaReadSpec` (`Tok`, `rdCap`)
and of `UnsafeRead{Scheduled,Finished}Compact.spec` (98/99-line proofs), plus:
- the anchoring, one clause in the contract's read post, proved in the bridge;
- restore's two call sites move after the `RLock` (they already are, textually: `:85-89`).

Either way it is the user's (trust base).

**R6-2 (the plan's precedent; docs).**
- The plan (`:720-723`) says the cindex's `metaReadTx` (`etcdserver/InvCindex.lean:207`) is "proved
  over the real backend through the hook's keys" and is "the precedent to follow".
- It is not proved over the real backend. `CindexBackend.lean:27-30`: "The reads of `ReadTx`
  (`isMetaBackend`) stay a premise".
- It has the same token-free shape (`{{ True }} RLock {{ True }}`, `InvCindex.lean:207-210`).
- So there is no token-threaded precedent. The cindex's premise has the same mismatch with the real
  `readTx.RLock`. Where that premise is discharged for the real backend (`InvBoot.lean:366`'s
  field, `SnapApplyDefs.lean:117`) I did not trace (**uncertain**). If it rests on an axiom, it is
  R6-1's twin: record it for the cindex's owner.
- Correct the plan's sentence.

### The compaction's read token at wiring (`writerOwn` → `store.Compact.spec`)

Go: `store.Compact` takes `s.mu`, then `checkPrevCompactionCompleted` does
`s.b.ReadTx(); tx.RLock(); defer tx.RUnlock()` (`mvcc/kvstore.go:224-232, 272-275`). The only Go
caller is the apply thread, through `watchableStore` and the applier's `Compaction`.

The options, not decided:
- **(i) `store.Compact.spec` lends `storeRT γ` (= `kbRT γ.kb`, `InvStore.lean:1442, 1536`), given
  back in every branch.**
  - The apply thread holds one in `writerOwn` (`InvStore.lean:3453-3461`, `writerOwn_rt` lends it)
    and calls `Compact` synchronously, so it is free there.
  - The sibling precedent: `store.restore`'s spec takes `RT` from its caller
    (`store__restore.lean`, spec line 70).
  - Over mvcc's assumed backend, `kbRT none = True`, which costs nothing.
  - Cost: one conjunct in the pre and the post of `store.Compact.spec` and `watchableStore`'s
    `Compact`, and one `writerOwn_rt` at M2's call site.
  - A client-visible change, so the user's.
  - This is the cheapest, and local: the resource the code touches, from the one caller.
- **(ii) A slot of the readers' pool (`readerPool`, `idxSlot`, `InvStore.lean:2894-2900, 2962`),
  checked out inside `Compact`.**
  - Checkout takes a ticket (`readerPool_checkout`), which the caller would still have to supply,
    so the spec changes anyway.
  - It makes `Compact` a pool client. Not cheaper. (Ticket mechanics read from docstrings only:
    **uncertain**.)
- **(iii) A dedicated token in `s.mu`'s resource.**
  - `NewStore` would need one more `kbRT` than `actualMaxReaders`.
  - The backend's opener gives exactly one per reader slot (`newPostK`, `InvNew.lean:160`), so
    there is no spare.
  - Not available without changing the backend's constructor.

## Target 5: the `BParams.VI` design (`backend-cmp-plan.md:750-757`)

### What is good

- **It is needed.** `checkPrevCompactionCompleted`'s and `restore`'s `BytesToRev` panics on a
  malformed value (`mvcc/revision.go:98-109`: length, separator, sign). So a reader of `Meta`'s
  compaction keys needs their form, and the backend is where it can be kept.
- **It is pure and decidable:** `VI n k v := n = Meta ∧ metaCompactKey k → metaRevVal v`. That is
  good for the tester: a put's `P.VI n k v` premise is checkable per call.
- **It is in the existing vocabulary's style:** a per-instance pure parameter like
  `HB`/`SB`/`HK`/`RB`, not a client `IProp`. So it is not the HoCAP shape the principles warn
  against, though it is a client-chosen invariant parameter.
- **The default `fun _ _ _ => True`** keeps every other instance's obligations trivial.
- **Holding it until question (2) is decided is right:** alone it closes nothing.

### Findings

**R6-3 (preference "know what it rests on"; the trust base). The cost list misses the openers.**

*Why the openers are affected.*
- `viOk` goes into `safeSt` over the committed contents.
- `isBackend` carries `safeSt`. `storage.OpenBackend`'s axiom gives
  `newPostK γ P W Pk K b D ⊢ isBackend γ P …` for the file's arbitrary `D`
  (`InvNew.lean:156-161`; `openPre` has no condition on `D` beyond `hkData`,
  `InvOpen.lean:84-88`).
- So with `VI` in `safeSt`, that axiom would assert `viOk P.VI D` of any database file. It becomes
  stronger, silently, through a definition it mentions.

*The repair.* A premise `⌜viOk P.VI D⌝` in `openPre` (a trust-base statement change: the user's),
and the same in `backend.New`'s proved spec. The callers discharge it:
- the bootstrap's empty file, trivially;
- a received image, from `keyImage`'s "neither key" (`Image.lean:41-44`);
- a restart over an existing data directory: an assumption about the disk's contents. That is the
  kind of assumption `noCmpData` already is, and is today out of scope, since `NewStore` needs
  `kbNoCmp`.

Add this to the plan's cost list and to question (3) in the user's batch.

*The rest of the cost list I checked:*
- `BParams` is built in 4 places (`hookMax :=`);
- 12 proof files use `batchTxBuffered.UnsafePut/UnsafeSeqPut.spec` (the plan says "13+");
- `safeSt` has 17 occurrences in `Proof`.

**R6-4 (preference "know the margin"; design alternative, not a defect).**
- If (a′) is chosen, the readers' `rv` already carries `Meta`'s physical contents. Then `VI` could
  be stated as a law of `rv` at a hold (`rtHeld … rv ⊢ ⌜viOk P.VI rv⌝`) and need not be a clause
  on every session state.
- But the batch lock's states must keep it for the law to hold at a later hold, so `safeSt` (or the
  commit lemmas) still carry it. The saving is the readers' law only.
- I would not redesign for it. I note it so the choice between (a′) and the plan's (a) is made
  with `VI` in view: both need `VI` for the non-`nc` read.

## What remains before the Freeze

The exit condition is "every `…C` replaced". Three statements remain:
1. `batchTxBuffered.Unlock.specC`, blocked on question (1);
2. `batchTxBuffered.UnsafeDelete.specC`, blocked on question (1);
3. `isKeyBackendG_of_backendC`, with two `sorry`s:
   - the limited range (`:2614`), which needs (2) above;
   - `metaReadTx` (`:2662`), which needs question (2) as restated (R6-1), then `BParams.VI` with
     R6-3's `openPre` premise (question 3).

The fold list (`backend-cmp-plan.md`, with rounds 4-6):
- R4-4's monotonicity lemma with R5-3's `SR`/`SRh`, and `Del'` instantiated directly;
- the old bridge as its instance; drop `bridge_crt`, `bridge_rt`, `bridge_rt_clean`;
- `hHK` from `bridgeParams` or a `KBReal` lemma (R6-5);
- the compaction over the real backend: `kbCmp := True`, the job, `SetScheduledCompact`/
  `SetFinishedCompact` off mvcc's assumed backend, and `store.Compact.spec`'s read token (the
  wiring question above: the user's);
- O5 (`Cmp` removed) and both fix sites to `dlReg_fix` (R5-6);
- the trust-base items in the user's batch:
  - the `Snapshot` axiom's `viewAt` (question 1);
  - `kbNoCmp_metaNone` (question 2, R6-1);
  - `openPre`'s `viOk` (question 3, R6-3);
  - F3's bbolt `Delete_kv` `own` (round 1).

**What can proceed without the user: little.**
- The plan's text: R6-6, R6-2, R5-1/2/3/5's in-place corrections.
- R6-5.
- Possibly R4-4's lemma statement, written but not used, so its `sorry`s reach nothing.

Every remaining `sorry` waits on a user question. That is the point to send the batch.

## Bugs in the Go code

None. Nothing for `issues/`. `BytesToBucketKey`'s panic on a malformed `Meta` value is a corrupt
database's behavior, not a bug.

R6-1 is a bug in this repository's trusted statement, not in Go. Per `CLAUDE.md` it belongs in
`notes/`: the plan, and `notes/STATUS.md`'s trust-base line when it is decided.

## Ranking (most need of revision first)

1. **`kbNoCmp_metaNone` and question (2)** (R6-1, R6-2).
   - The axiom is false as stated today, and doubly so after M2.
   - Neither of the plan's options repairs it as worded.
   - Restate the question with an anchored, hold-scoped form (a′) before it goes to the user.
2. **`BParams.VI`'s design** (R6-3, R6-4). Its cost list must include `openPre`/`OpenBackend`'s
   premise, a trust-base change.
3. **The user's batch as written** (R6-6). Questions (1)-(3) should be in one place, with
   superseded text marked: (b) and `relog` are wrong where the user reads them first.
4. **The new bridge's `hHK`** (R6-5), minor.
5. **`metaPutCap` and its callers; `keyView_thin`, `bridge_crtC`/`bridge_rtC`, the slot triples,
   `bt_metaPut`.** Right as they are.

## Verified vs uncertain

**Verified** (Lean read, Go read, `lake build --no-build`):
- **The build.** The round compiles (the three modules up to date). Two `sorry`s are left in the
  bridge, which is linked nowhere.
- **`metaPutCap`'s new form** and its two callers' proofs. Go keeps the slices (`tx_buffer.go`) and
  never writes them after the put (`mvcc/store.go`). `UnsafePut.spec` already requires `↦*□`.
- **`hHK`.** True of `KBReal.P` (the four key strings), and needed for `hkPut`.
- **R6-1's counterexample.** The axiom's binders are free, and `keyReadSnap`/`keyReadSnapC` with
  `L := False` hold of any `rt` (definitions read). `restore` applies the axiom before `RLock`;
  `ReadTx()` returns one `readTx` per backend.
- **The cindex's `metaReadTx`.** Token-free, and a premise, not proved
  (`CindexBackend.lean:27-30`).
- **`newPostK` carries `isBackend` over the opened `D`,** and `openPre` has no data premise
  (R6-3's basis).
- **The read token.** `writerOwn` holds `storeRT`; `restore`'s spec takes `RT` from its caller;
  `NewStore` takes exactly `actualMaxReaders` `kbRT`s.
- **R5-4 is done.** R5-1/2/3/5/6 are recorded but not corrected in place.

**Uncertain:**
- **That R6-1 yields `False` in Lean.** I believe not: the backend's specs leave a hook bucket's
  reads unpinned. The finding is falsity of the code, not inconsistency.
- **Whether Perennial's model makes a lock-free `UnsafeRange` racing a write-back UB** (R6-1's
  first sub-point).
- **Whether the backend's `readTx.UnsafeRange` spec gives `rv`'s contents for a hook bucket,**
  which (a′) needs.
- **Where the cindex's `isMetaBackend` premise is discharged** for the real backend.
- **The readers' pool's checkout mechanics** (option ii above), read from docstrings only.
- **That bbolt's `Put` never writes the caller's slices.** I did not re-read bbolt; the buffered
  path alone forces `↦*□`.
- **That no `sorry` of the stage reaches a linked result.** I did not run `etc/tcb-report.py`. The
  bridge has no user outside its file.
