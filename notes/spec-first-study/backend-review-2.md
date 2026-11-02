# backend-cmp, Review round 2 (2026-10-29)

Commit under review: `b6d5f6b791` (branch `backend-cmp`), the round-1 repairs `6cdfe63e31..b6d5f6b791`
(`699bc59950` F3/F6/F8/F9, `57b4463794` F1/F2, `b6d5f6b791` F4/F10). Round 1:
`notes/spec-first-study/backend-review-1.md`; decisions: `notes/backend-cmp-plan.md`, "After Review
round 1". Go: etcd at `.lake/go-src/etcd` (`964dccdb42`; `server/storage` as at the pin, round 1),
bbolt v1.5.0 at `~/go/pkg/mod/go.etcd.io/bbolt@v1.5.0`. `lake build --no-build` of
`store__scheduleCompaction` and `backend.Link` reports everything up to date at `HEAD`, so the
changed proofs compile. Everything else below is "verified" in the sense that I read it in the code
or the Lean source; I proved nothing new.

## Summary

The repairs fix what they target:
- **F1/F2**: the range lends against a per-call `T` and hands out the delete over its own `Rd`.
- **F3**: true of bbolt and minimal.
- **F6**: `dlNone` is gone, and `dlInit_noDel` is proved.
- **F8, F9**: fixed.

But the new budget (F4) is still unprovable, for two independent reasons:
- **R2-1**: a stale stock from an earlier session is spendable.
- **R2-2**: the stock does not count the session's `Key` puts. With `P.limit ≤ 2^57`, a session can
  reach `pend = 2^58 - 1` and then fail `Unlock`'s premise.

Both problems, and F5's 54 re-proofs, come from one choice: after the deletes, the session goes back
to the general `Locked l` (`T -∗ Locked l`). The lessor's delete already avoids this with a token
that only `Unlock` takes (`unlockAt`, `InvStore.lean:993-1004`). Copying that precedent gives a
cheaper and sound statement (R2-3). It needs no `DP` parameter, no `dpStock`, no change to
`LockOutsideApply`, and leaves `bkLocked` and its uses as they are.

## Round 1's findings at `HEAD`

| | Status |
|---|---|
| F1 (lending against `Locked l`) | **Fixed** in the statement (`InvStore.lean:1101-1121`: `T ∗ (T -∗ Locked l)`, `rdCap Rd T`, `rdCap2 Rd T`). Provable only with a new `Locked` (F5) or R2-3. |
| F2 (caller-chosen `Rd`) | **Fixed**: the delete is returned inside the range's post, over the range's own `Rd` and `T` (`:1116-1120`). With F3 the bridge passes `txBytes` directly and no longer needs to read the key under `T`. |
| F3 (bbolt `Delete_kv` of a transaction's own key) | **Fixed**; true and minimal (Target 3). One gap remains in the internal layer: R2-6. |
| F4 (per-key permits at a free name) | **Not fixed**: the restatement is unprovable for new reasons (R2-1, R2-2), and the job is proved only for `DP = True` (R2-5). |
| F5 (the new `Locked`) | **Recorded, open.** A cheaper statement is in R2-3. |
| F6 (`dlNone` linked to nothing) | **Fixed**: `dlNone` and `BNames.dln` are dropped. `dlInit_noDel` is stated and proved (`DelKeys.lean:93-98`). The route to D22's readers is open (Target 4). |
| F7 (`▷` and who fixes `Φ`) | **Recorded, open.** On the form, see Target 4. |
| F8 (`Unlock.specC` and the write buffer) | **Fixed** (`batchTxBuffered__Unlock.lean`, the diff's lines 621-632). `viewSame P st` is exactly `thinV_refl` plus the new conjunct (`Model2.lean:280-282`), so dropping branch 1 loses nothing. |
| F9 (`srSlot` twice) | **Fixed**: `backend.srSlot`/`srHeld` (`DelKeys.lean:133-146`). `kbSR` uses it (`InvStore.lean:1433`). |
| F10 (`kbWTSupply` from `srvWTPool`) | **Restated in the docstring only**: the job gets its own pool. A new coupling to D22 is hidden (R2-7). |
| F11 (positional `dlInit`) | **Open** (recorded). |

## Target 1: mvcc's compaction clauses (`batchTxSpecG`, `InvStore.lean:1063-1131`) and `bkDP`

### What is good

- **The per-call token is the right shape.** It is the point read's pattern (`:1087-1093`), so
  bbolt's slices are lent for one session only. Over bbolt, `T := ∃ st, batchLocked … st ∗ ⌜st.tx =
  tx₀⌝ ∗ …` gives `txLive tx₀ 1` through `ownWTxG_live` (`InvBbolt.lean:131-133`).
  - `rdCap`/`rdCap2` follow from `txBytes_acc` (`:124-126`), with `txLive` split in halves for the
    two slices (`txLive_fractional`).
- **Returning the delete inside the range's post** removes the caller-chosen `Rd` (F2) and keeps the
  clause count at nine.
- **The job's glue stayed small.** It threads `T` through its loop invariant (`"Hlocked" ∷ T`,
  `store__scheduleCompaction.lean:531`) and takes the lock back once, after the loop (`:571`). The
  delete is one `iapply` (`:458`).
- **The Go structure supports a per-session budget.**
  - `Unlock` commits whenever a delete is pending (`batch_tx.go:355`:
    `t.pendingDeleteOperations > 0`), so each deleting session resets `pending`.
  - The job's operations per session are at most `batchNum`: a full batch is at most `batchNum`
    deletes and no `Meta` put; the last batch is fewer than `batchNum` deletes plus one put
    (`kvstore_compaction.go:58-71`).
  - So `CompactionBatchLimit ≤ dpStock` is the exact requirement, with no off-by-one.

### Findings

**R2-1 (hard: sound against the implementation; F4 not fixed). A stock from an earlier session is
still spendable.**
- `bkDP gp n := ownToks gp n` (`BackendBridge.lean:2118`) is at one name `gp`, a plain parameter of
  the bridge (`:2269`), for every session.
- `LockOutsideApply` gives `DP dpStock` every time (`InvStore.lean:1101`). No clause takes a stock
  back: `Unlock`'s pre is `Locked [] ∗ W ∗ P` (`:1077`).
- So a caller that keeps a remainder `DP r` from session 1 can spend it in session 2 beside session
  2's own `DP dpStock`. The contract's delete accepts any `DP (n + 1)`, and the bridge cannot tell a
  stale fragment from a fresh one.
  - `ownToks` is additive (`TokSet.lean:46-51, 124-136`).
  - The authority `●` can only count outstanding fragments, which grow without bound across
    sessions.
- So the sessions' operations are unbounded, and neither `UnsafeDelete.specC`'s `pend + 1 < 2^58`
  nor `Unlock`'s `pend + hookMax < 2^58` can be derived. The `sorry` "minted with the new `Locked`'s
  authority" (`BackendBridge.lean:2310-2312`) is not provable as the contract stands.
- The job itself drops its stock (`store__scheduleCompaction.lean:318`, `-`). Soundness is
  ∀-callers, though.

*Restatement*: make the budget part of the session, not a backend-wide name. Either:
- R2-3 (the budget is local to the range call); or
- `DP` holds half of an exclusive per-backend ghost variable naming the current session, with
  `LockOutsideApply` taking the previous `∃ n, DP n` back. This threads a resource through every
  caller, so R2-3 is better.

**R2-2 (hard: sound; the bound's arithmetic). The stock does not count the session's `Key` puts.**
- In the contract, `UnsafeSeqPut` (`:1071-1076`) is usable in a `LockOutsideApply` session, both
  before the range and after `T -∗ Locked l`, with no `DP`.
- `bkLocked`'s `sessPuts` allows `pend < P.limit + l.length` with `l.length ≤ 2^56`
  (`BackendBridge.lean:136-138`). `keyPutOk` gives `l.length < 2^56` per put (`:1606-1607`). `P.Wf`
  allows `P.limit ≤ 2^57` and `hookMax ≤ 2^16` (`Model2.lean:66-68`).
- The worst session:
  - `pend` starts at `≤ 2^57 - 1`;
  - `2^56` puts bring it to `≤ 2^57 - 1 + 2^56`;
  - `2^56` deletes or `Meta` puts bring it to `≤ 2^58 - 1`.
- `Unlock` then needs `pend + hookMax < 2^58`, which fails for any `hookMax ≥ 1`. etcd's hooks
  write the consistent index, so `hookMax ≥ 1` for the server's `P`.
- So even a fresh, unshared stock of `2^56` leaves no room.

*Restatement*: either:
- the compacting range takes `Locked []` (the job's case) and the session cannot return to
  `Locked` (R2-3), so no puts follow; or
- `dpStock := 2^55`, with the scope premise `CompactionBatchLimit ≤ 2^55`
  (`2^57 + 2^56 + 2^55 + 2^16 < 2^58`).

**R2-3 (preference: caller burden and size; F5, the cheaper statement). End a deleting session with
an `Unlock`-only token, as the lessor's delete does.**
- The lessor's `Lease` delete returns `∃ U, U ∗ unlockAt bt View W P U l` (`InvStore.lean:1124-
  1130`, `unlockAt` at `:997-1004`): "a token only `Unlock` takes". The bridge proves it over
  `bkLockedD` (`BackendBridge.lean:147-153`) without touching `bkLocked`.
- The compaction job needs nothing more. Go's session is `LockOutsideApply`, then one range, then
  deletes, then at most one `Meta` put, then `Unlock` (`kvstore_compaction.go:55-91`).
- Proposed clause:
  ```
  □ (⌜Cmp⌝ -∗ ∀ q m b lo hi klo khi limit dqlo dqhi,
      ⌜0 < sint.Z limit ≤ 2^56 ∧ khi ≠ []⌝ →
      {{ Key ↦□ b ∗ Locked [] ∗ View q m ∗ lo ↦*{dqlo} klo ∗ hi ↦*{dqhi} khi }}
        UnsafeRange(b, lo, hi, limit)
      {{ ks vs, RET (ks, vs); View q m ∗ lo ↦* … ∗ hi ↦* … ∗
         ∃ m' Rd (U : Nat → IProp), U ((sint.Z limit).toNat + 1) ∗ snapThin m m' Del ∗
           rdCap2 Rd (U _) … ∗ pairVals Rd ks vs (…take limit) ∗
           □ (∀ key k n, {{ Key ↦□ b ∗ U (n+1) ∗ Del k ∗ □ Rd key k }} UnsafeDelete {{ U n }}) ∗
           □ (∀ key val k v n …, ⌜metaCompactKey k ∧ metaRevVal v⌝ →
                {{ Meta ↦□ b ∗ U (n+1) ∗ key ↦* k ∗ val ↦* v }} UnsafePut {{ U n ∗ … }}) ∗
           □ (∀ n, {{ U n ∗ W ∗ P }} Unlock {{ True }}) }})
  ```
  (`rdCap Rd`/`rdCap2 Rd` stated at every `U n`, or `U` taken as `∃ n`, as convenient.)
- What this gains:
  - **The bound is local and sound.** The session leaves `Locked []` once and never returns, so it
    makes at most `limit + 1` operations after a start below `P.limit ≤ 2^57`. `2^57 + 2^56 + 1 +
    2^16 < 2^58`.
  - **R2-1 and R2-2 go away**, and so do the contract parameter `DP`, `dpStock`,
    `LockOutsideApply`'s `DP dpStock` and the separate `Meta`-put clause's `DP`.
  - **The scope premise sits on the Go argument** (`limit ≤ 2^56`), at the call that needs it. The
    job gets it from `isStore`'s `Hcfgl` (`InvStore.lean:3242`). This is "a premise the code needs"
    in the place the code needs it.
  - **`bkLocked` keeps `ndel = 0`, and its 54 uses are untouched.** The new proofs are the range, the
    delete, the `Meta` put and the `Unlock` over a new `bkLockedC` with `ndel`, the deleted keys'
    `dlIs` and the count. The `Unlock` goes through `Unlock.specC` branch 2.
  - **`Unlock.specC`'s branch 3 can stay exact** (R2-4).
- What it costs:
  - The contract is weaker than `T -∗ Locked l`: no puts or second range after a delete. No caller
    does either (Go and the job). So this is the right trade under "prefer the stronger spec,
    comparing whole specs" only because the stronger one has no caller and costs 54 re-proofs plus
    R2-2's arithmetic.
  - `UnsafeSetFinishedCompact.spec` takes `Locked l` over `batchTxSpec` (its spec file, `:31-38`), so
    it must be restated over a token with the `Meta`-put clause. It must change anyway (R2-5).
  - The job's loop holds `U` to the end instead of `T` (`:531`). Its last batch calls the `Meta` put
    and then `Unlock` under `U`; a full batch calls `Unlock` under `U`.

**R2-4 (hard, forward: complete; holds only under the current `T -∗ Locked l`). `Unlock.specC`'s
clients'-view branch is exact.**
- Branch 3 hands back `bView γ 1 (sData P st.S)`, the physical contents (the diff's line 630).
- Under `T -∗ Locked l`, a session can delete and then put, and end with the contract's puts-`Unlock`
  (`InvStore.lean:1079-1083`). That clause promises `View 1 (foldl l m)`, the logical view, which
  differs from `sData` by the deleted keys.
- So with the current statement, branch 3 would also have to become thin (`bView γ 1 L ∗ thinV …
  (sData) L`). Under R2-3 no session reaches branch 3 after a delete.

**R2-5 (hard: complete; the plan's claim is inaccurate). The job is proved only for `DP = True`.**
- The job runs over `storeBackend` (`InvStore.lean:3313-3315`). Its `isKeyBackendG` takes the
  defaults: `DP = True`, `SR = SRh = True`.
- So it passes `%0` and frames `DP 1` with `iframe #` (`store__scheduleCompaction.lean:458-459`).
  `UnsafeSet{Finished,Scheduled}Compact` do the same (`%0`, their spec over `batchTxSpec`).
- The plan says the job is "unchanged but for passing `n`" (`backend-cmp-plan.md`, F4 entry). That
  is not true of the real backend:
  - `storeBackend` must take the real `DP`/`SR`;
  - the job's loop must carry the remaining count;
  - it needs `CompactionBatchLimit ≤ dpStock`;
  - the two `UnsafeSet…Compact` specs must take and return the budget.
- Under R2-3 it is the count inside `U`, and the same reasoning applies.

*Where the scope premise must go* (either design):
- `isStore`'s `"%Hcfgl"` (`InvStore.lean:3242`), beside `0 < limit`;
- established in `NewStore` (`NewStore.lean:120-126`, where `0` becomes the default `1000`,
  `kvstore.go:44, 92`) from a new premise on `cfg`;
- carried by the results that already carry `hcfg : 0 ≤ CompactionBatchLimit'`:
  `StoreBackend.lean:81`, `mvcc/Results.lean:256`, `BuildLemmas.lean:63`,
  `etcdserver/Results.lean:814, 881, 1022`.

It is needed only where the backend counts, i.e. by the real backend with the compactor on. Under
"no unneeded premise", scope it to that instance (a conjunct of `compactTok`/the `kb = some d`
budgets) rather than to every `NewStore`.

Go's `pending` is an `int` that only wraps, so Go has no such bound. The `2^58` belongs to the
backend's proof. The premise is a scope restriction: record it in a decision. It is not a Go issue.

## Target 2: `batchTxBuffered.UnsafeDelete.specC`, `Unlock.specC`, `DelKeys`

### What is good

- **`Unlock.specC`** (F8) is now one deleting branch plus the clients'-view branch. The added
  conjunct is `viewSame`'s second part verbatim, so branch 1 really is the instance `thinV_refl`.
  - It is true of Go: the deleting session always commits (`batch_tx.go:355`).
  - Readers between the write-back and the commit hold the old bbolt transaction, which still has
    the deleted keys. That is a superset of the physical view and inside the logical view.
- **`dlInit_noDel`** is exactly round 1's F6(b): no later, and proved
  (`saved_pred_valid_2`, `DFrac.valid_own_op_discard`).
- **`srSlot`/`srHeld`** are one definition in the backend.

### Findings

**R2-6 (hard, Draft-level: complete). The internal `batchTx.UnsafeDelete.spec` was not widened.**
- `batchTxBuffered.UnsafeDelete.specC` now takes `(if own then key ↦*{dk} kb else txBytes st.tx key
  kb)`. Its body is `t.batchTx.UnsafeDelete(…)` then `pendingDeleteOperations++`
  (`batch_tx.go:418-421`).
- Its callee's spec still takes `key ↦*{dk} kb` only
  (`Spec/…/backend/batchTx__UnsafeDelete.lean`, the `abbrev`). Only that proof changed, passing
  `own := true` (`batchTx__UnsafeDelete.lean:73-76`).
- So `specC` with `own = false` cannot be proved from it. This is internal to the backend and only
  needs the same `own` flag (`btW γ t st` holds the `ownWTxG` the widened `Delete_kv` needs).

**R2-8 (minor: preference "the margin").** `txBytes` is persistent (`InvBbolt.lean:104`), so
returning it in the `own = false` posts is redundant. It is harmless, and kept for symmetry with
`own = true`.

## Target 3: bbolt's `Bucket.Delete_kv` (F3, a trust-base change)

**True of bbolt v1.5.0** (verified in `~/go/pkg/mod/go.etcd.io/bbolt@v1.5.0`):
- `Bucket.Delete` (`bucket.go:498-533`) reads `key` through the logger, `c.seek(key)` and
  `bytes.Equal`, then calls `c.node().del(key)`.
- `node.del` (`node.go:145-159`) does a `sort.Search` with `bytes.Compare`, and
  `n.inodes = append(n.inodes[:index], n.inodes[index+1:]...)` moves inode headers. No byte array is
  written.
- Materialising a node (`node.read`) reads page memory and does not write it. Pages are not remapped
  or rewritten before `Commit`'s spill.
- So a key slice the same transaction's cursor returned keeps its bytes, and `txBytes tx key kb` holds
  after the call.
- etcd's `unsafeRange` appends the cursor's keys uncopied, so `keys[i]` is such a slice.

**Minimal**: one Boolean `own`, a case split on the input, which the principles allow. The owned case
is unchanged, and so is its only other user (`batchTx.UnsafeDelete`'s proof; `grep Delete_kv`:
there is no other caller).
- A disjunction `key ↦* kb ∨ txBytes …` would give callers a disjunction back. The flag is the better
  form, so the author's judgement call on it is right.

**Recording**:
- `etc/tcb-baseline.txt` lists axioms by name (`:348`), so `--check` does not see a statement change.
- No `interface/` file covers bbolt (no `etc/api` for it).
- So the change is visible only in the diff and the docstring. Put it in `notes/decisions.md` (or the
  stage's merge note) explicitly, as the user's decision says, together with the planned tester case.

## Target 4: `dlInit` and D22's exact readers; `isKeyBackendG_congrDel`

**Can `dlInit` reach D22's exact readers additively? Only partly** (uncertain in the details; I did
not trace every D22 flow).
- `dlInit` is the registration's whole fraction: exclusive.
- `SnapApplyWalk.lean:283-284` and `BootBackend.lean:85-87` currently discard it.
- Routing it to `store.Restore`'s clean read (`Spec/…/store__Restore.lean:126-128`, beside
  `kbViewC`/`kbNoCmp`) adds an exclusive conjunct to D22's restore resources and to their positional
  destructurings. That is a statement change, though additive, and it is F11's burden again.
- The snapshot sender reads the running backend, possibly concurrently with other readers. An
  exclusive token cannot be shared, which is round 1's open uncertainty.

*Cheaper and sound*: a persistent exactness witness, the registration fixed at `False`.
- The holder of `dlInit` who will never compact (the restore's new backend; the boot backend with
  the compactor off) runs `dlReg_fix γ (fun _ => False)`.
- Readers use a law `dlReg γ (fun _ => False) ∗ dlIs γ nk ⊢ ▷ False`, from `saved_pred_agree`. Inside
  any WP or update, `▷ False ⊢ ◇ False` discharges it.
- Being persistent, it goes into D22's persistent bundles (`#`, `iframe #`). Concurrent senders
  share it, and no ownership flow changes.
- Keep `dlInit_noDel` for whoever still holds the unfixed registration.

**`isKeyBackendG_congrDel` "under `▷`"** (the author's first judgement call: right that a later is
needed, but `▷` is the wrong form).
- `Del` occurs positively inside persistent, non-update contexts: `snapThin`'s `□ ∀ k v, ⌜…⌝ -∗ Del k`
  (`InvStore.lean:613-615`), which is in the range's post. A congruence that turns `bkDel k` into
  `▷ delKey k` there can't strip the later.
- The direction `delKey k ⊢ bkDel k` needs no later (`dlIs` takes `□ Φ nk`). Only
  `bkDel k ⊢ ▷ delKey γ k` has one.
- Recommended: instantiate the store's `Del` as `fun k => ◇ delKey γ k` and state
  `□(∀k, Del k -∗ ◇ Del' k) ∗ □(∀k, Del' k -∗ Del k)`. `◇` rather than `▷`: if `delKey` is timeless,
  `▷ delKey ⊢ ◇ delKey` with no step. The readers then add one `imod` before their
  `iunfold mvcc.delKey` (`storeTxnCommon__rangeKeys.lean:729-731`).
- *Uncertain*: whether `crevLb` is `Timeless`. `idxCert` has an instance
  (`InvRequest.lean:605`); I found none for `crevLb`.

## Target 5: `kbWTSupply` (F10)

**R2-7 (hard, forward: complete; the "no coupling to D22" claim). The job's own pool competes with
D22's pool for one finite stock.**
- The supply's statement (`InvStore.lean:1444-1447`) is provable for a fixed `d` from an invariant
  `∃ a n, ⧗ a ∗ ownToks d.γB.wb n ∗ ⌜receiptBound ≤ a + n + 1⌝`, as `srvWTPool` does
  (`InvApplier.lean:815-819, 950-964`). It needs no `E.γbe` share and no counter.
- The docstring's "valid only while the backend does not change" is not the constraint: tokens of a
  fixed `d` stay sound.
- The constraint is the stock. Each pool needs about `receiptBound` tokens of `γB.wb`. The backend
  makes `wbInit = 2^40 - 1` (`InvNew.lean:36`), and D22 already spends nearly all of it:
  - `SnapApplyWalk.lean:90`: `receiptBound ≤ wbInit - 6`;
  - `bootBackend_of_newPost`'s `N + 7 ≤ wbInit` with `receiptBound ≤ N + 1` (`Results.lean:2225`,
    `InvApplier.lean:866`).
- A second pool needs `wbInit ≥ 2·receiptBound + 7`. That changes D22's premises
  (`receiptBound ≤ (wbInit - 7) / 2`, or a larger `wbInit`), or the two pools must share one stock.

*Restatement*: say so in the plan, and choose before the wiring step:
- (a) halve D22's `receiptBound` premise, a statement change to D22's results; or
- (b) in the compactor-on configuration (backend fixed), let the job take from D22's pool with the
  agreement fixed to the boot backend. *Uncertain*: whether `wbInit` can simply grow; its `2^40`
  bound's reason is not stated where it is defined.

## Ranking (most need of revision first)

1. **mvcc's compaction clauses with `DP`/`dpStock`/`bkDP`** (R2-1, R2-2, R2-5): unprovable as
   stated. R2-3 replaces the budget, the return to `Locked` and F5's 54 re-proofs with one local
   token.
2. **`kbWTSupply`** (R2-7): the stock split with D22 is a statement change to D22 that the plan does
   not show.
3. **D22's exactness and the `Del` congruence** (Target 4): prefer a persistent `dlReg γ False`, and
   `◇` over `▷`. Decide before the wiring step.
4. **`Unlock.specC` branch 3** (R2-4, only if `T -∗ Locked l` stays) and the internal
   `batchTx.UnsafeDelete.spec` (R2-6).
5. **bbolt `Delete_kv`**: true and minimal. Record the change in the decisions, since the baseline
   check does not see it.
6. **`Unlock.specC` branch 2, `dlInit_noDel`, `srSlot`/`srHeld`, `thinV`**: fine as they are.

## Verified vs uncertain

**Verified** (code or Lean read; the changed proofs build at `HEAD`):
- bbolt's `Delete` writes no key bytes, so a same-transaction key slice stays valid.
- `Unlock` commits whenever a delete is pending.
- The job makes at most `batchNum` operations per session.
- `ownToks` is additive, and no clause reclaims a stock.
- `P.limit ≤ 2^57`, `l.length ≤ 2^56` and `hookMax ≤ 2^16` give R2-2's overflow.
- `storeBackend` uses the default `DP`/`SR`.
- `batchTx.UnsafeDelete.spec` is not widened.
- `viewSame` = `thinV_refl` + the new conjunct.
- `srvWTPool`'s stock and `receiptBound ≤ wbInit - 6`.

**Uncertain**:
- `crevLb`'s timelessness (the `◇` congruence).
- Whether D22's exact reads are concurrent (which the persistent witness makes moot).
- Whether `wbInit` can grow.
- The exact D22 flows `dlInit` would traverse.
- R2-3's cost to `UnsafeSetFinishedCompact`'s callers (`store.go:53` too).

**No new Go bug.** `pending` only wraps (`int`), and the bound is the proof's own.
