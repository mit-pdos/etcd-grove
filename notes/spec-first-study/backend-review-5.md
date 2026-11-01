# backend-cmp, Review round 5 (2026-10-29)

**Commit under review.** `fa1bf63593` (branch `backend-cmp`, worktree `/shared/etcd-grove-be`).
The changes since round 4 are `a6e184655e..fa1bf63593`, four commits:
- `d15ac9cf49`: R4-1, `dlInit` in the statements, fixed inside;
- `85eab57b4b`: R4-3, R4-5/6, and R4-4 recorded;
- `964a23fe72` and `fa1bf63593`: R4-2 measured, then held for the user.

Round 4's report is `notes/spec-first-study/backend-review-4.md`.

**Go.** Read at the pin: `/shared/etcd-grove/.lake/go-src/etcd/server/storage/{backend,mvcc,schema}`.

**Build.** I did not build. Every changed module's `.olean` (`ReadLemmas`, `ReadSide`, `DelKeys`,
`InvBackend`, `StoreBackend`, `BuildLemmas`, `NewServer`, both `Results`, the `Unlock` spec) is
newer than its source, so the round compiled. I did not run `etc/tcb-report.py`, because it writes
`.lake/tcb.json`. So "no `sorry` of this stage under a result" is **uncertain** here, as in round 4.

What I did check: the five `sorry`s of the stage are all in `isKeyBackendG_of_backendC`
(`BackendBridge.lean:2293, 2295, 2321, 2325, 2352`). The only other new `sorry` relative to `lean`
is M2's `NewServer.specCompact` (`NewServer.lean:1980`), which is not this stage's.

## Summary

Round 4's repairs are right.
- **R4-1 is fixed, in the right place.** The statements are mode-free.
- **R4-3 is fixed.**
- **The R4-4 statement as recorded is correct about `Del` and `Cmp`.** It is imprecise about
  `SR`/`SRh`: the old and new bridges differ there.

The held item is where the substance is.
- **R4-2's planned `relog` is wrong for non-safe-range deletes.** The fix is one restriction, which
  should be written into the plan before the user decides.
- **Of the two `viewAt` options**:
  - (a) is sound;
  - (b) is unsound as worded ("another split of `γ.view`": shares of one ghost variable agree), and
    is sound only with a new ghost name.
- **A hazard in both cases.** Moving the batch quarter onto `L` while `viewAt` stays the plain
  quarter would make the `Snapshot` axiom false after a compaction.
- **The decision also touches the trust base**, through that axiom's meaning, not only D22's
  statements.

The stage is not close to Freeze:
- three `…C` statements remain;
- the old bridge, the compaction over the real backend and O5 are open.

Four of the bridge's five `sorry`s look independent of the held decision. Per "Batching", the stage
can go on with them.

## Round 4's findings at `HEAD`

| | Status |
|---|---|
| R4-1 (`dlNoDel` in top-level statements) | **Fixed** (`d15ac9cf49`); details below. |
| R4-2 (`Unlock.specC` branch 2 and the two commit lemmas at the physical view) | **Open, held for the user** (it moves D22's `viewAt`). The plan's form needs one repair (R5-1). |
| R4-3 (`thinV_rebase` without `h2`) | **Fixed** (`ReadLemmas.lean:152-185`). The old lemmas it replaces are now dead (R5-4). |
| R4-4 (old bridge by monotonicity) | **Recorded** (`backend-cmp-plan.md:632-640`), not written. The statement is right in `Del`/`Cmp` but must let `SR`/`SRh` change (R5-3). |
| R4-5 (stale docs) | **Fixed** in `DelKeys.lean`'s header and `Unlock.specC`'s docstring. `STATUS.md`'s current header says `dlInit` (its old `dlNone` text survives only in the "Before it" chain, which is history). One residual: it says the flag is fixed "by servers that do not compact"; it is now fixed by the store (`NewStore_backend`, `server_kv_watchable_of`). Trivial. |
| R4-6 (`dlNoDel` vs `bkNoCmp` comments) | **Fixed** (`InvBackend.lean`, `dlNoDel`'s docstring; `DelKeys.lean`, `dlNoDel_fix`). |

## Target 1: R4-1's fix, and the exported statements against `lean`

### What is good

- **The statements take the unfixed registration; the flag is fixed below them.**
  - The statements: `mvcc.NewStore_backend` (`StoreBackend.lean:88-90`), `server_kv_watchable_of`
    (`BuildLemmas.lean:69-71`), and the linked `mvcc_NewStore_backend` (`mvcc/Results.lean:263-265`),
    `server_kv_backend`, `server_kv_watchable` and `server_kv_backend_hooks`
    (`etcdserver/Results.lean:822-824, 891-893, 1043-1045`).
  - Where it is fixed: `dlNoDel_fix` at `StoreBackend.lean:116` and `BuildLemmas.lean:101`,
    immediately before `storeBackend_of_backend`.
  - `NewServer.wp_proofM` no longer fixes it. It passes `Hdl` from `bootBackend_of_newPost`
    (`NewServer.lean:508, 583, 588`).
  - This is the user's F6/F7 route, restored.
- **The fix is where the mode is chosen.** Over the real instance the store's mode is
  `kbCmp (some d) = False` (`InvStore.lean:1597`, `kbCmp kb := kb = none`), consumed through
  `storeBackend_of_backend`'s `hc`. M2's compacting store will instead fix
  `dlReg γB (late-bound delKey)` at the same line, before `NewStore` allocates `γ`. That is the plan
  §2's route through the store's registration, as `lateW d.gx`. So the precondition of these
  statements need not change again.
- **The exported statements against `lean` (merge base `0bb0334b84`).** I diffed every `Results.lean`
  and the examples. The only differences are:
  - `dlInit d.γB` in `mvcc_NewStore_backend` and the three `server_kv_*` results;
  - `batchLimitOk` in place of `0 ≤ CompactionBatchLimit` (those four, plus `NewServer.spec`,
    `specCompact`, `specM` and mvcc's `New`/`NewStore`/`newWatchableStore` specs; the examples
    discharge it, `newServer.lean:77, 178`, `startServer.lean:96`);
  - `dlNoDel` in the old bridge's two exports, `mvcc_backend_bridge` and
    `mvcc_storeBackend_of_backend` (`mvcc/Results.lean:223, 311`).

  So the plan's sentence (`backend-cmp-plan.md:622-625`) is accurate for the closed theorems. It is
  right to keep the function-spec changes out of it, which are listed elsewhere for the user's
  batch:
  - `ConcurrentReadTx.spec`'s post is thin;
  - `UnsafePut`/`UnsafeSeqPut` require "above C";
  - `batchTx.UnsafeDelete` and bbolt's `Delete_kv` take `own` (F3: trust base);
  - `UnsafeSet{Scheduled,Finished}Compact` go over `metaPutCap`.
- **The premises are right.**
  - **`dlInit`** is exclusive, unfixed and supplied by the backend's constructor. Any creator holds
    it, so it is a precondition every caller can meet.
  - **`dlNoDel` on the old bridge** is right. That bridge has `¬ Cmp` and an arbitrary `Del`: with
    an arbitrary `Del`, the readers' `snapThin m m' Del` is only provable if nothing is missing, and
    `dlNoDel` + `thinV_exact` gives exactly that. The bridge goes away at O5, so its premise is not
    a mode written into a lasting statement.
  - **`batchLimitOk`** is the user's (2026-10-29).

### Findings

**R5-5 (minor, docs).** The plan lists `keyCleanRead_of_backend` among "the old bridge's exports"
(`backend-cmp-plan.md:624`). It is not in `mvcc/Results.lean`. Its one user is D22's
`SnapApplyWalk.lean:383`. Say "and `keyCleanRead_of_backend` (D22's restore)".

**R5-6 (minor, structure).** The flag is fixed in two lemmas, `NewStore_backend` and
`server_kv_watchable_of`, because `server_kv_watchable_of` calls `storeBackend_of_backend` itself
instead of going through `NewStore_backend`. M2 must change both. A one-line note in the plan's
fold list ("M2: both fix sites") is enough.

## Target 2: R4-3, `thinV_rebase`'s new premise at its one use

### What is good

- **The new lemma is true and proved.**
  - The statement: `thinV γ (vData P (C, X)) L ∗ thinV γ (vData P (C', R.reset)) L ⊢
    thinV γ (vData P (C', X)) L` (`ReadLemmas.lean:167-185`).
  - Its pure core, `vData_rebase_or'`, has no hypothesis (`:152-162`): per key, `X`'s own value, or
    `dget C'`, which is `vOf (C', R.reset)` (`vOf_reset`).
  - This is exactly what round 4 proposed.
- **The one use** (`ReadSide.lean:626-628`, `rtRes_cm_close`, no-window case) supplies the new
  premise as `thinV (vData P (C', R.reset)) (vData P (C, R))`. It gets it by rewriting the old
  `Hth` with `hview rfl`. That is correct, and for now it is the only way, since the no-window case
  still carries `hview`.
- The lemma no longer depends on the view being kept. So group 2's deleting commit, where `hview`
  fails, can use it unchanged, with the new state's thinness from the registered deletes.

### Findings

**R5-4 (preference "after a change, drop what existed only for it"). `vData_rebase`
(`ReadLemmas.lean:108`) and `vData_rebase_or` (`:132`) have no users left** (`grep -rnw` over
`Proof`/`Spec`). Delete both, and rename `vData_rebase_or'` to `vData_rebase_or`.

## Target 3: R4-2's planned form (the batch quarter onto `L`, `relog`)

The plan (`backend-cmp-plan.md:641-660`):
- `batchGhostAt`'s quarter is `∃ L, viewQ γ ¼ (vData P (st.C, st.R)) L`;
- a put session's `Unlock` sets
  `L' := relog L st`, `(relog L st).lookup nk = (sData P st.S).lookup nk <|> L.lookup nk`;
- a deleting session keeps `L`.

### What is good

- **The direction is right.**
  - Compaction leaves mvcc's logical bucket unchanged: the limited range's deletes leave the view
    as it is (`batchTxSpecG`, "the view unchanged", `InvStore.lean:1076-1078`), and `snapThin`
    only lets readers *miss* keys.
  - So after a compaction, the clients' `bkView γB 1 m` (`keyView vd m`) must keep the compacted
    revisions. `relog`'s fallback to `L` keeps them.
- **Under `bridgeParams` it gives exactly mvcc's bucket.** At the lock, the physical view is thin of
  `L` and `keyView L m` holds. So in `Key`:
  - a key the session put reads its put;
  - a committed, uncompacted key reads its `C` value, which equals `L`'s (thin's first clause);
  - a compacted key reads `L`'s value.

  That is `foldl insert puts m`, which `Unlock`'s branch 2 must give.
- **A single existential `L` in `batchGhostAt`** keeps `batchLocked`'s 97 uses textually unchanged.
  Ghost agreement then equates the batch's and the readers' `L`. This is the cheapest form, and an
  internal choice, so the agent's to make.
- **A deleting session keeps `L`, and the new physical view is thin of it.** The missing keys are
  registered: `UnsafeDelete.specC` requires `dlIs` on a safe-range delete. The cached states rebase
  through the new `thinV_rebase`. This is consistent with Target 2.

### Findings

**R5-1 (hard rule "sound", for the group-2 statement; the plan's text). `relog`'s fallback to `L` is
wrong at a key the session deleted from a bucket that is not safe-range.**

*The evidence.*
- `UnsafeDelete.spec` allows a delete in any bucket that is not safe-range (`P.SB = false`).
  `Unlock.spec`'s branch 2 quantifies over every `P`. In Go, sessions delete such keys:
  - `schema/auth_users.go:49`, `auth_roles.go:65`, `alarm.go:81`, `lease.go:59`;
  - `actions.go:48` (`Meta`).
- At such a key, `sData P st.S` has no entry (deleted) while `L` does. So `relog` keeps the key in
  the logical view.
- The new physical view then misses a key that no one registered (`dlIs` is only ever given for
  safe-range deletes). So `thinV phys L'` is unprovable, and a branch-2 `Unlock` whose session
  deletes such a key would have an unprovable post.
- The same breaks the promised `relog_noDel` (`relog = sData` under `dlNoDel`, round 4's
  restatement): it fails exactly at such a key.

*The callers affected.* None today: under `bridgeParams` every bucket but `Key` is `HB`
(`BackendBridge.lean:101-106`), so outside `vData`. But the spec is general, and D22's and the
auth proofs pass it on.

*Restatement.* Fall back to `L` only in safe-range buckets, whose deletes are all registered:
```
(relog P L st).lookup nk = (sData P st.S).lookup nk <|> (if P.SB nk.1 then L.lookup nk else none)
```
Then:
- `thinV (sData P st.S) (relog P L st)` holds: the missing keys are safe-range keys missing from
  the physical view at the lock, or deleted in-session, all registered;
- under `dlNoDel` there are no safe-range deletes and nothing missing at the lock, so
  `relog = sData`. This needs a per-bucket form of `sessWf_C_in_S`: its `ndel = 0` hypothesis is
  global, and a session may have deleted a `Lease` key. I have not checked that in Lean
  (**uncertain**).

Also fix the plan's parenthesis "compacted keys stay out of mvcc's bucket" (`:651`). Under this
definition they stay **in** the logical bucket, which is what mvcc needs.

**R5-2 (hard rule "sound"; the trust base). The two `viewAt` options.**

*The setting.* `viewAt γ vd := ghostVar γ.view ¼ vd` (`InvSnapshot.lean:129`). It is the batch
lock's quarter. `backend.Snapshot.spec` is an axiom (D22 S-f, `backend__Snapshot.lean`): from an
observation `R -∗ W -∗ Pk -∗ viewAt γ vd -∗ … -∗ ⌜Q vd d r⌝`, it gives `Q (sData P D) …` for the
committed `D`. Its justification (`backend__Snapshot.lean:33-39`) is that at each commit the lock's
share "was `viewAt γ (sData P C)`".

- **The hazard (both options must avoid it).** Suppose group 2 moves the batch quarter to `L` and
  leaves `viewAt` as the plain quarter. Then after a compaction the share is `viewAt γ L` with
  `L ≠ sData P C`. The axiom would derive `Q (sData P D)` from an observation that held only of
  `L`, and would be **false**: take `Q vd := (vd = L₀)`.
  - So `viewAt` cannot be left alone. Either its definition changes or its ghost name does.
  - Either is a change to what a trusted statement means. That makes it the user's under "Who
    decides" (trust base), in addition to the D22 owner's.
  - The plan presents it only as a D22 question. Add the trust-base reason.
- **Option (a): `viewAt γ vd := ∃ L, ghostVar γ.view ¼ L ∗ thinV γ vd L`. Sound.**
  - At each commit the committer holds the quarter at `L`, and the committed `sData P C` is thin of
    it: that is the `viewQ` invariant the group adds.
  - The axiom's premise only gets weaker for the caller to discharge (less is known of `vd`), so the
    axiom gets no stronger.
  - It costs D22 nothing today. The only user, `SnapSendBranch.lean:211`, discards the `viewAt`
    hypothesis (`- Hbl - Hhk Hr`).
  - Caveat to the plan's wording "D22's users exact through `dlNoDel`": on the boot backend,
    `dlNoDel` is now made inside `server_kv_watchable_of`/`NewStore_backend` and not returned. A
    future D22 user needing an exact `viewAt` there would need those lemmas to return `dlNoDel`, a
    statement change. Nobody needs it now.
- **Option (b) as worded ("another split of `γ.view`") is not sound.**
  - All shares of the one `ghostVar γ.view` agree on a single value. So a D22 share at the physical
    view and the batch's share at `L` cannot coexist after a compaction.
  - It works only with a **new ghost name**: a physical committed-view variable, its own share in
    the batch lock, updated at every commit.
  - That costs a second update in each commit lemma (`InvCommit.lean`, `NewAlloc.lean`,
    `ReadSide.lean` closes) and a new `BNames` field.
  - It keeps the `Snapshot` axiom's text, but `viewAt`'s definition and docstring still change.
- **Assessment (not a decision).** Both (a) and (b)-with-a-new-name are sound. (a) is smaller and
  its only user is unaffected. Put the options to the user as (a) or (b′), with (b) restated as a
  new ghost name.

## Target 4: the R4-4 monotonicity statement, as recorded

The recorded statement (`backend-cmp-plan.md:633-637`):
```
isKeyBackendG … Del … Cmp … ∗ □ (∀ k, Del k -∗ Del' k) ∗ □ (⌜Cmp'⌝ -∗ ∀ k, Del' k -∗ Del k) ⊢
  isKeyBackendG … Del' … Cmp' …        (Cmp' → Cmp)
```

### What is good

I checked every occurrence in `isKeyBackendG` (`InvStore.lean:1295-1328`), `isBatchTxG` (`:1202`)
and `batchTxSpecG` (`:1091-1162`).
- **`Del` is positive in all of these:**
  - `keyReadSnap`'s `snapThin m m' Del` (`:718-723`, `:613-615`);
  - the point read's `Del k ∗ ks ↦* []` disjunct;
  - the limited range's `snapThin`.
- **`Del` is negative only** in the limited range's delete triple (`Del k` in its pre), which is
  under `⌜Cmp⌝`.
- **`Cmp` occurs only as `⌜Cmp⌝ -∗`**, in three places: the limited range, the standalone `Meta`
  put, and the safe-range lock with `metaReadTx`.
- **So the statement is true:** with `Cmp' → Cmp`, the first hypothesis covers the positive uses
  and the second the negative one under `Cmp'`. It is more general than round 4's `¬ Cmp'` form,
  and correct.

### Findings

**R5-3 (hard rule "special cases are instances"; the plan's statement). The elided parameters
cannot all stay fixed.**
- The new bridge has `SR := backend.srSlot b`, `SRh := backend.srHeld b`
  (`BackendBridge.lean:2286`). The old bridge has the defaults `True`/`True`
  (`mvcc/Results.lean:224-227`).
- `SR`/`SRh` occur in both polarities, but only under `⌜Cmp⌝`.
- So the lemma must let them change:
  - with `SR' SRh'` free and `□ (⌜Cmp'⌝ -∗ (SR' ∗-∗ SR) ∗ (SRh' ∗-∗ SRh))`;
  - or with a hypothesis `Cmp' → SR' = SR ∧ SRh' = SRh`.
- Otherwise the old bridge is not an instance.

Also: the plan derives the old bridge "with `Del' := fun _ => False`". The old bridge's exports are
over an *arbitrary* `Del` (`mvcc_backend_bridge`'s binder). Instantiate `Del'` with that `Del`
directly: `bkDel γ k ⊢ False ⊢ Del k` by `dlNoDel_noDel`. One step, not two.

The decision not to write it before the new bridge's cases are proved is right: otherwise the
cases' `sorry`s would reach every server result.

## Anything false the statements rest on

- **Nothing false at `HEAD`.** Round 4 checked the Go facts the thin view rests on:
  - deletes are unbuffered (`batch_tx.go:418-421`);
  - only compaction deletes `Key` (`kvstore_compaction.go:62` is the only `UnsafeDelete(schema.Key,
    …)` in `mvcc`, `backend` and `schema`; checked again);
  - the commit's reset keeps `bufVersion`.

  All still hold.
- **The `Snapshot` axiom is true today**, because the batch quarter is still exact. It becomes false
  under group 2 unless `viewAt` moves with the quarter (R5-2). This is the one place where an
  unchanged statement could silently become false.
- **The F3 trust-base change (bbolt `Delete_kv`'s `own`)** is unchanged since round 1: the user's,
  to be covered by the Test step's bbolt tester. I did not re-read bbolt.

## Is the stage close to Freeze?

No. The exit condition, "every `…C` replaced", has three statements left:
1. `batchTxBuffered.Unlock.specC`: needs R4-2, held for the user;
2. `batchTxBuffered.UnsafeDelete.specC`: its safe-range case needs the batch quarter at `L`, so it is
   also blocked on R4-2;
3. `isKeyBackendG_of_backendC`, with its 5 `sorry`s.

The rest of the fold list (`backend-cmp-plan.md:475-480`, as amended by round 4):
- the R4-4 monotonicity lemma, with R5-3's `SR`/`SRh`;
- the old bridge as its instance; the old bridge's exact read proofs (`bridge_crt`, `bridge_rt`,
  `bridge_rt_clean`) then go;
- the compaction proved over the real backend (the job, `updateCompactRev`; `SetScheduledCompact`/
  `SetFinishedCompact.spec` off mvcc's assumed backend), with `kbCmp := True`;
- O5 (`Cmp` removed). At that point the old bridge's exports with `dlNoDel` disappear, and both
  fix sites (R5-6) change to `dlReg_fix`.

**What can proceed now ("Batching": the stage goes on with what does not depend on the user).**
These look independent of R4-2:
- the new bridge's two read cases (`:2293, 2295`): the readers' side is already over `L`, and
  `snapThin m m' (bkDel γ)` follows from `thinV` and `keyView L m`;
- probably the `Meta` value-invariant case (`:2325`) and the slot/`metaReadTx` case (`:2352`).

The limited range's case (`:2321`) needs `UnsafeDelete.specC`, so it waits. I did not check the
`Meta`/slot cases' dependencies in detail (**uncertain**).

## Ranking (most need of revision first)

1. **R4-2's plan** (R5-1, R5-2):
   - `relog` must fall back to `L` only in safe-range buckets;
   - the `viewAt` options must be restated: (b) needs a new ghost name, and the question is also a
     trust-base one (the `Snapshot` axiom);
   - leaving `viewAt` as is would make that axiom false.

   These are plan fixes now, statement changes at the fold.
2. **The R4-4 statement** (R5-3): let `SR`/`SRh` vary, and instantiate `Del'` directly.
3. **Dead lemmas and docs** (R5-4, R5-5, R5-6).
4. **R4-1's fix, the exported statements, `thinV_rebase`:** right as they are.

## Bugs in the Go code

None found. Nothing for `issues/`.

## Verified vs uncertain

**Verified** (Lean or Go read):
- **R4-1's placement.** `dlInit` is in the six statements and fixed at the two sites. `NewServer`
  passes it unchanged. `kbCmp (some d)` is `False`.
- **The exported statements against `lean`.** Their only differences are `dlInit`, `batchLimitOk`,
  and the old bridge's `dlNoDel` (diff of every `Results.lean`, the `NewServer` and mvcc
  constructor specs, the examples).
- **`thinV_rebase`.** Its new statement and proof, and its one use.
- **Dead lemmas.** `vData_rebase` and `vData_rebase_or` are unused.
- **Polarity.** `Del`'s and `Cmp`'s polarity in `isKeyBackendG`/`batchTxSpecG`/`keyReadSnap`, and
  the `SR` mismatch between the bridges.
- **`viewAt`.** Its definition, the `Snapshot` axiom's statement and justification, and the one user
  discarding `viewAt`.
- **Go's `UnsafeDelete` callers.** Non-safe-range sessions delete (`schema/*.go`). The only `Key`
  delete is compaction's.
- **The build.** Every changed module's `.olean` is fresh.

**Uncertain:**
- That no `sorry` of the stage reaches a linked result: I did not run `etc/tcb-report.py`.
- `relog_noDel` under R5-1's restriction: it needs a per-bucket `sessWf_C_in_S`, argued, not proved.
- Which of the new bridge's `Meta`/slot cases are independent of R4-2.
- The cost estimate of option (b′) (the new ghost name): counted from the plan's list of quarter
  sites, not measured.
