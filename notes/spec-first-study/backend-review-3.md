# backend-cmp, Review round 3 (2026-10-29)

Commit under review: `600f7d12e6` (branch `backend-cmp`, a merge of `lean`). The stage's own changes
since round 2 are `52d403048b..4088b5d960`: `ed40251049` (R2-3's token, `batchLimitOk`) and
`4088b5d960` (R2-6, `dlReg_false_noDel`, `delKey_timeless`, R2-7's docstring, F3 recorded). Round 2:
`notes/spec-first-study/backend-review-2.md`. Decisions: `notes/backend-cmp-plan.md`, "After Review
round 2" and its "Decided by the agent" list.

Go: etcd at `/shared/etcd-grove/.lake/go-src/etcd` (`server/storage/{backend,mvcc}`). bbolt v1.5.0
as in round 2.

**Build.** The `.olean`s in the worktree are newer than their sources at `4088b5d960` for
`InvStore`, `DelKeys`, `BackendBridge` and `store__scheduleCompaction`. The merge changed none of
the storage files (`git diff 4088b5d960 600f7d12e6 -- Proof/.../storage Spec/.../storage` is
empty), so the stage's changed proofs compiled. The merge did change `etcdserver/{Results,
NewServer}.lean` (auth's C1). Those were not rebuilt here, so the post-merge server build is
**uncertain**; I did not build. "Verified" below means read in the Go code or the Lean source; I
proved nothing new.

## Summary

R2-3 is done well and closes R2-1, R2-2, R2-4 and F5:
- the compacting range takes `Locked []` and returns a counted, delete-only token `U : Nat → IProp`;
- the job's loop threads it with one invariant;
- `UnsafeSet{Scheduled,Finished}Compact` are one spec each over `metaPutCap`.

The token form is true of Go and sufficient for the job. No statement in the diff rests on
something false that I could find.

What remains is mostly forward and about process:
- **The fold list is incomplete** (R3-1). It misses the mvcc-side twin: the whole compaction path
  is still proved only over mvcc's assumed backend, through `isKeyBackendG_cmp` and the
  `batchTxSpec` instance. So "R2-5 dissolved" is only half true.
- **`batchLimitOk` on every store is defensible on substance, but it is the user's call** (R3-2).
  It changes `NewServer.spec` and the closed results, it departs from the repair the user wrote
  down, and the decisions entry credits the placement to the user.
- **Stale or wrong docstrings** (R3-3, R3-4).

## Round 2's findings at `HEAD`

| | Status |
|---|---|
| R2-1 (a stale stock spendable across sessions) | **Stale**: `DP`, `dpStock` and `bkDP` are gone (`grep` finds none in `Proof/`, `Spec/`). The budget is per call, inside the range's `U`. |
| R2-2 (`Key` puts not counted) | **Fixed**. The range takes `Locked []` (`InvStore.lean`, the clause after `LockOutsideApply`), so the session has made no put before it and can make none after (`U` allows only a delete, the `Meta` put and `Unlock`). Arithmetic: `sessPuts` gives `pend < P.limit ≤ 2^57` at `Locked []` (`BackendBridge.lean:136-138`, `Model2.lean:66-67`); at most `limit + 1 ≤ 2^56 + 1` operations follow; `+ hookMax ≤ 2^16` stays `< 2^58`. |
| R2-3 (the delete-only token) | **Done** as proposed (Target 1). |
| R2-4 (`Unlock.specC` branch 3 exact) | **Stale**: no session reaches the clients'-view branch after a `Key` delete any more. The lessor deletes from `Lease`, which is an `HB` bucket (`bridgeParams`, `BackendBridge.lean:103`), so `vData` does not see it. |
| R2-5 (the job proved only for the assumed backend's defaults) | **Half fixed.** The budget part is gone: the job is generic in `U` (`store__scheduleCompaction.lean:345-347, 381`). The rest is open. The job still goes through `isKeyBackendG_cmp` (`:233`), i.e. `RT = WT = True` and `SR = SRh = True`. See R3-1. |
| R2-6 (`batchTx.UnsafeDelete.spec` not widened) | **Fixed**: the flag `own`, passed through to `Delete_kv` (`batchTx__UnsafeDelete.lean:73-75`). `batchTxBuffered.UnsafeDelete`'s proof instantiates `own := true` (`:47-49`). |
| R2-7 (two pools, one stock) | **Restated in the docstring** per the user's decision (Target 5). The statement is unchanged and correct; D22's change is listed, not made. |
| R2-8 (`txBytes` returned redundantly) | Unchanged; harmless. |
| Target 3 (record F3) | **Done**: `notes/decisions.md`, "bbolt's `Bucket.Delete_kv` takes a key of its own transaction". |
| Target 4 (`dlReg γ False`; `◇` congruence) | **Laws added**: `dlReg_false_noDel` (`DelKeys.lean:108-117`) and `delKey_timeless` (`InvStore.lean:1853`). Neither is used yet (the wiring step). |
| F11 (positional `dlInit`) | Open, as recorded. |

## Target 1: the delete-only token (`batchTxSpecG`'s compacting range, `metaPutCap`, the standalone `Meta` clause, `UnsafeSet…Compact.spec`)

### What is good

- **True of Go.** The session is `LockOutsideApply`, then one `UnsafeRange(Key, last, end,
  batchNum)`, then deletes, then at most one `UnsafeSetFinishedCompact`, then `Unlock`
  (`kvstore_compaction.go:55-91`). Nothing commits inside the session:
  - `batchTx.UnsafeDelete` and `UnsafePut` only do `t.pending++` (`batch_tx.go:229-246`, `:190`);
  - only `batchTxBuffered.Unlock` commits (`:328-355`).

  So the range's bbolt slices stay valid until `Unlock`. That covers `rdCap Rd (U n)` for every `n`,
  including the job's `h.WriteKeyValue(keys[i], values[i])` *after* deleting `keys[i]`
  (`:62-65`), given round 2's bbolt reading (`node.del` moves inode headers only). Nothing reads a
  slice after `Unlock`: `rev` is a copied value and `h` keeps only a hash state.
- **The count is right, with one unit of slack.** The job makes at most `batchNum` operations per
  session:
  - a full batch is `≤ batchNum` deletes and no put;
  - a short batch is `< batchNum` deletes plus one put.

  `U (limit + 1)` allows one more. That is harmless (the bridge's arithmetic has room) and keeps
  the job's invariant one conjunct. Per "Know the margin", the docstring could say the code needs
  only `limit`.
- **The job's glue is small and right.** The loop invariant is `∃ c, U c ∗ ⌜L.length + 1 ≤ c + i⌝`
  (`:381`).
  - At a delete `i < L.length`, so `c ≥ 2` (`:466-468`, `obtain ⟨c'', rfl⟩`).
  - After the loop `i = L.length`, so `c ≥ 1` for the `Meta` put (`:551-553`).
  - The last batch spends it through `HMetaC` (`:561`). Both batches end with `HUnlU` (`:576`,
    `:659`).
  - The added glue is about 20 lines. No clause of `bkLocked` is touched, so F5's 54 re-proofs are
    gone.
- **`metaPutCap`** is one definition for both tokens. `UnsafeSet{Scheduled,Finished}Compact.spec`
  became shorter and more abstract: `∀ bt X Y value`, `{{ metaPutCap bt X Y ∗ X }} … {{ Y }}`,
  with no `View`/`Del`/`W`/`Locked` binders. Each caller instantiates it in one line
  (`SetScheduledCompact.lean:51-52`, the job's `:558-561`). These are mvcc-internal helpers (the
  only callers are `SetScheduledCompact`, `SetFinishedCompact` and the job; etcdutl's
  `v3_snapshot.go:417` is not translated), so the agent was entitled to decide this.
- **The standalone `Meta` clause from `Locked []` only** is true and enough.
  - Its Go callers open a fresh session: `SetScheduledCompact` (`store.go:38-42`, from
    `kvstore.go:213`) and `SetFinishedCompact` (`store.go:50-54`; no Go caller outside tests).
  - The `Unlock` that follows works under `unlockAt … []`. In the bridge, `Meta` is an `HB` bucket,
    so `vData`/`sData` ignore it (`Model2.lean:172-180`) and the session is `viewSame`: branch 1 of
    `Unlock.spec`.
  - The same holds for the job's last batch through `Unlock.specC` branch 1: its "no puts to non-`HB`
    buckets" condition allows the `Meta` put.

### Findings

**R3-3 (preference: "no constant or conjunct whose reason you do not know", here the docstring).
`batchTxSpecG`'s docstring still describes the old compaction clauses.** The paragraph
"**Compaction** (2026-10-13, unit 5a …)" (`InvStore.lean`, just above `def batchTxSpecG`) still says:
- `UnsafeDelete(schema.Key, k)` "leaves the token as it is";
- the limited range returns "read-only slices";
- the `Meta` put "leaves the token as it is".

All three are false of the clauses now: the delete is from `U (n+1)` to `U n`, the slices are lent
under `U n`, and the `Meta` put goes to `U n` or to an `Unlock`-only token. A reader of the contract
reads that paragraph first. *Restatement*: replace it with the range-to-`U` story from the in-clause
comment, and say that the fresh-session `Meta` put ends in `unlockAt`.

## Target 2: `batchLimitOk` on every store (`NewStore`, `New`, `newWatchableStore`, `NewServer`)

**On substance: acceptable.** The range clause is one statement for every instance of the contract,
and it carries `limit ≤ rangeLimitMax`. The job is proved against that one contract, so every store
whose job can run needs the premise.

Scoping it to the real backend's compacting instance would need one of two things:
- a contract parameter (a per-instance bound, `∞` for the assumed backend); or
- an `isStore` conjunct conditioned on `kb`.

Either is machinery for a bound no real configuration approaches: etcd's default is 1000, and the
examples pass `0`, which `NewStore` turns into the default (`newServer.lean:77`, `:178`,
`startServer.lean:96`). It is a scope restriction that is marked and filed (`notes/decisions.md`,
"The store's batch limit at most 2^56"), which is what the "no unneeded premise" rule allows. I would
keep it uniform.

**R3-2 (process, "Who decides"; the user's call).**
- **It changes top-level statements.** `etcdserver/NewServer.spec` (`Spec/.../NewServer.lean:142,
  286, 434`) and the closed results' `hcfg` (`etcdserver/Results.lean:814, 881, 1022`;
  `mvcc/Results.lean`) now carry it. The table's right column lists "top-level statements" as the
  user's.
- **It departs from the repair the user recorded.** "After Review round 2" lists "the scope premise
  … scoped to the real backend's compaction instance".
- **Its attribution is wrong.** The decisions entry's header reads "taken (the user's: decision O3,
  its premise placed after review round 2)". The plan lists the item under "Decided by the agent",
  and the entry's last sentence admits the placement departs from the suggestion. The placement was
  the agent's.

*Restatement*: put it in this round's question batch to the user (keep it uniform, as argued above,
or condition it on `kb`). Change the decisions entry's header to "decided by the agent, pending the
user".

**R3-4 (minor, documentation).**
- `batchLimitOk`'s docstring says a negative limit "would make the job's loop read nothing". That is
  wrong. The backend treats a non-positive limit as unlimited (`batch_tx.go:207-209`), so the first
  pass reads everything and the loop never ends (`issues/etcd-compaction-negative-batch-limit.md`,
  "What happens"). Say "loops forever (the issue)".
- `etcdserver/Results.lean:792` still describes the premise as `0 ≤ CompactionBatchLimit`.

## Target 3: `batchTx.UnsafeDelete.spec`'s `own`, `dlReg_false_noDel`, `delKey_timeless` / `Del := ◇ delKey`

### What is good

- **`own`** mirrors `Delete_kv`'s flag and passes it straight through. The `if` sits on the input
  (a case split, not a disjunction of specs). Go's `batchTx.UnsafeDelete` touches the key only
  through `bucket.Delete(key)` (`batch_tx.go:229-246`), so the widening is true.
- **`dlReg_false_noDel`** (`DelKeys.lean:108-117`) is the persistent, shareable law round 2 asked
  for. It is proved from `saved_pred_agree` with the later kept (`▷ False`), which any WP or update
  strips.
- **`delKey_timeless`** (`InvStore.lean:1853`) holds by `infer_instance` after unfolding `idxCert`
  and `crevLb` (both ghost lower bounds plus pure facts). So `▷ delKey ⊢ ◇ delKey`, and
  `Del := ◇ delKey` costs the readers one `imod`.

### Findings

None blocking. One forward note (uncertain about cost, which looks small): with `Del := ◇ delKey`,
the two `⊢`-lemmas that consume `Del` become `◇`-conclusions:
- `crevUB_noDel` (`InvStore.lean:1898`) gives `◇ False`;
- `snapThin_crev` (`:1908`) gives `◇ (crevUB ∗ ⌜m' = m⌝)`.

Their callers (2 in `InvStore`, 1 in `rangeEvents.lean`) and the two reader sites that unfold
`delKey` (`storeTxnCommon__rangeKeys.lean:730`, `store__scheduleCompaction.lean:457`) are inside WPs,
so each needs one `imod`. Do this in the wiring step together with `isKeyBackendG_congrDel`.

## Target 4: `kbWTSupply` (one stock with `srvWTPool`)

**The statement is unchanged and right** (`InvStore.lean:1469-1472`: `□ (⧗ 1 ={⊤}=∗ wbTok d.γB)`).
The docstring's argument holds:
- every token costs a global receipt (`receipt_add_one_lt`, in `srvWTPool_take_extra_d`,
  `InvApplier.lean:1037-1056`);
- so one stock bounded by `receiptBound` serves every taker;
- `srvWTPool_bound` (`:1081`) needs only `applied ≤ a`, which extra takers keep.

**Forward (recorded, to the D22 owner; not a new finding).**
- Every existing take, e.g. `srvWTPool_take_extra_d`, needs a share `dghostVar E.γbe dq d` to agree
  on the current backend. A *persistent* conversion holds no such share.
- So `NewServer` can give `kbWTSupply` only if `srvWTPool`'s invariant gets a persistent agreement on
  `d` in the compactor-on configuration (e.g. `E.γbe` frozen at boot when no snapshot can be
  installed).
- That is a mode clause in D22's invariant: allowed as state (`ρ.kv.cmp`), but it is a D22 statement
  change.

The docstring says this ("srvWTPool's invariant exposing the receipt-to-token conversion at the boot
backend when the compactor is on"). Make sure it is in the user's batch and STATUS's "for the D22
track" line, since the user's R2-7 decision only said "one stock".

## Target 5: the remaining `…C` variants and the fold plan (the one-spec rule)

**No new twin was added this round. That is right.** `metaPutCap` serves two clauses with one
definition, and the `Meta` clause now has a single form.

The plan's per-variant notes are correct as far as they go:
- `UnsafeDelete.spec` is the instance of `specC` at `own = true` and `SB = false`.
- `Unlock.spec` follows from `specC` through `thinV_refl`.
- `UnsafeSeqPut.specC` has a *stronger* premise than `.spec`, so `.spec` is not its instance: `.spec`
  must go and its 13 caller files move. The plan says this ("changed in place").
- `safeStC` and `cacheValidC` fold with those.
- All four `…C` statements are unproved and unused (`isKeyBackendG_of_backendC` still takes the
  `.spec` versions, `BackendBridge.lean:2244-2266`), so no second proof exists yet.

**R3-1 (hard rule "one spec per function", forward; the plan's fold list is incomplete).**

The mvcc side has a twin the list leaves out: *the compaction is proved only over mvcc's assumed
backend*.
- `isKeyBackendG_cmp` (`InvStore.lean:2257-2262`), given `storeCmp γ` (`kbCmp kb := kb = none`),
  turns the store's contract into the instance with `RT = WT = True`, `noPutCond` and default
  `SR`/`SRh`.
- The job (`store__scheduleCompaction.lean:233`) and `store.updateCompactRev` (`:238`) go through it.
- `SetScheduledCompact.spec` and `SetFinishedCompact.spec` take `mvcc.batchTxSpec`, the
  assumed-backend instance (`Spec/.../SetScheduledCompact.lean:28-33`; `batchTxSpec` at
  `InvStore.lean:1229-1231`).

When the stores switch to `kbCmp := True`, `isKeyBackendG_cmp`'s conclusion is false of the real
backend: the real `LockInsideApply`/`LockOutsideApply` need `RT ∗ WT`. Then:
- `SetScheduledCompact.spec` and `SetFinishedCompact.spec` must be restated over `batchTxSpecG`
  (`RT`, `WT`, `PutOk`);
- the job must pay `RT`, `WT` (from `kbWTSupply`) and the slot (`kbSR`) per batch;
- `isKeyBackendG_cmp` and `compactJobPreR_none` go away or become instances.

So R2-5 is not "dissolved": its budget half is, but the tokens-and-slot half is the same work,
unlisted.

Two smaller gaps:
- The plan says the old bridge "is [the new one's] instance with `Cmp` false and goes". The old one
  is for any `Del` (`BackendBridge.lean`, the `Del` binder) and the new one for `bkDel γ`. The
  instance therefore goes through `isKeyBackendG_congrDel` (unwritten) and a fixed registration (at
  `delKey`, or at `False` for the compactor-off boot). List it as a step of that fold.
- `Cmp` itself (O5's later cleanup) is the mode-as-parameter the rule names. Its removal belongs on
  the same list.

*Restatement of the plan's list*: add
1. `isKeyBackendG_cmp`, `batchTxSpec`, and `Set{Scheduled,Finished}Compact.spec` over it: restated
   over `batchTxSpecG`; the job's budgets wired (`kbRT`/`kbSR`/`kbWTSupply` through `compactTok`);
2. `isKeyBackendG_congrDel` before deleting the old bridge;
3. `Cmp`/`kbCmp` (O5).

Make "every `…C` replaced, not kept beside" an exit criterion of the stage. **Who decides**: keeping
the four `…C` statements until their proofs is a structural choice (a parallel family). The plan
presents it as status ("none added; folding … not cheap now"). Put it to the user as a question in
this round's batch, with the exit criterion attached.

## Ranking (most need of revision first)

1. **The fold plan** (R3-1): the mvcc-side twin (`isKeyBackendG_cmp`, the `batchTxSpec`-instance
   specs) and the bridge's `congrDel` step are missing, and R2-5 is only half closed. It is a plan
   fix now, and a set of statement changes at the wiring step.
2. **`batchLimitOk`'s placement** (R3-2, R3-4): fine on substance, but a top-level statement change
   that departs from the user's recorded repair, and misattributed. Send it to the user and fix the
   two docstrings.
3. **`kbWTSupply`**: the statement is fine. The D22 change it needs (a persistent agreement on `d`
   in compactor-on mode) must reach the collaborator and the user.
4. **The token, `metaPutCap`, the `Meta` clause, the job's invariant**: right. Only `batchTxSpecG`'s
   stale "Compaction" paragraph to rewrite (R3-3), and optionally the `limit + 1` margin noted.
5. **`own`, `dlReg_false_noDel`, `delKey_timeless`**: fine as they are.

## Agent-decided items under "Who decides"

| Item | Verdict |
|---|---|
| `U : Nat → IProp` counting the budget | The agent's to take (an equivalent repair, internal). Fine. |
| `metaPutCap`; `UnsafeSet…Compact.spec` restated over it | The agent's (mvcc-internal helpers, no family, a smaller statement). Fine. |
| The `Meta` clause from `Locked []` only | The agent's (a contract clause no caller uses in the stronger form). Fine. |
| `batchLimitOk` on every store | **The user's**: it changes `NewServer.spec` and the closed results, and departs from the recorded repair (R3-2). |
| Keeping the `…C` variants until proved | **The user's** (structure). Presented, but as status rather than as a question (R3-1). |

## Verified vs uncertain

**Verified** (Go or Lean read):
- Nothing commits inside a compaction session before `Unlock`, so the range's slices (keys and
  values) stay valid across its deletes and the `Meta` put.
- The job makes at most `batchNum` backend operations per session.
- `pend < 2^57` at `Locked []`, and `2^57 + 2^56 + 1 + 2^16 < 2^58`.
- `Meta` is an `HB` bucket under `bridgeParams`, so both `Meta`-put sessions satisfy `Unlock`'s
  branch 1.
- The job's invariant arithmetic (`c ≥ 2` at a delete, `c ≥ 1` after the loop).
- `SetScheduledCompact`/`SetFinishedCompact` open their own session (`LockInsideApply`).
- No `DP`/`dpStock`/`bkDP` is left.
- `batchTx.UnsafeDelete`'s proof passes `own` through.
- `dlReg_false_noDel` and `delKey_timeless` hold as stated.
- `isKeyBackendG_cmp` is the job's and `updateCompactRev`'s route, and the `Set…Compact.spec`s take
  `batchTxSpec`.
- `srvWTPool`'s takes need a `γbe` share.
- The negative-limit behaviour (the issue's reading of `unsafeRange`).
- The stage's modules compiled at `4088b5d960` (`.olean`s newer than the sources; storage untouched
  by the merge).

**Uncertain**:
- The post-merge build of `etcdserver/{Results,NewServer}.lean` (changed by the merge, not rebuilt
  here).
- The bridge's two remaining new cases (the range's token, the `Meta` put) and the slot/`metaReadTx`
  case: still `sorry`, so whether `U := bkLockedC …` proves them depends on the thin-view invariants
  not yet written (consistent with the Go reading above, not checked in Lean).
- The exact shape of D22's `srvWTPool` change.
- The `◇ delKey` cost beyond the sites counted.

**No new Go bug.** `issues/etcd-compaction-negative-batch-limit.md` already covers the negative-limit
case, which the new docstring misdescribes (R3-4).
