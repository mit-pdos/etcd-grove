# backend-cmp, Review round 1 (2026-10-28)

Commit under review: `28b1f62b8d` (branch `backend-cmp`), the diff `10e2918d3e..28b1f62b8d`.
Go: etcd at the pin `249d76bea` (read with `git show 249d76bea:…` in `.lake/go-src/etcd`, whose
checkout is at `964dccdb42`; the two differ in `server/storage` only in tests), bbolt v1.5.0
(`~/go/pkg/mod/go.etcd.io/bbolt@v1.5.0`, the version `server/go.mod:25` names). No earlier round, so
no finding is stale. I did not build; "verified" below means read in the code or the Lean source, not
checked by Lean.

## Summary

The approach is right. mvcc's contract already treats the view as logical: deletions show only as
`snapThin … Del` in reads (`InvStore.lean:1022-1026`, the point read's `Del k` disjunct). mvcc's
readers already prove they never name a deletable key (`storeTxnCommon__rangeKeys.lean:727-739`,
`rangeAnswers_not_del`). So making the backend's `γ.view` logical brings the backend up to what mvcc
assumes. It does not weaken what any verified client relies on, with the exception of D22's exact
readers. The defaults (`DP`, `SR`, `SRh` = `True`) leave mvcc's assumed backend unchanged. Keeping
`…specC` and `isKeyBackendG_of_backendC` beside the old statements keeps the `sorry`s away from
existing results.

But four committed statements cannot be met by the real backend whatever proof is written. All
four are in the contract clauses the stage exists for:

1. The limited range lends its slices against `Locked l` itself (`rdCap Rd (Locked l)`), a token
   that comes back in every later session. The bbolt slices die at the commit (F1).
2. The `UnsafeDelete(Key)` clause quantifies over the caller's `Rd`. The bridge must give up all of
   `Locked l` to read the key, and then has no `batchLocked` left for the delete (F2). Underneath,
   bbolt's `Delete_kv` cannot take a key that lives in its own transaction (F3).
3. The delete permits `bkDP gp` are tokens at a ghost name the bridge owns nothing of. Even minted,
   they would not bound a session's deletes (F4).
4. `dlNone` is linked to nothing: neither the invariant nor `UnsafeDelete.specC` mentions it, and the
   whole fraction is the creator's. The exactness law it promises is not provable (F6).

These go to the author's two questions. **The lent-key delete clause is not strong enough.** It is
not too weak for the job; it is unprovable for the bridge. **`dlInit` does let a non-mvcc holder fix
the predicate.** That is harmless to soundness, but mvcc must then receive `dlInit` (or a matching
`dlReg`) to use it. And the `▷` of the agreement breaks the planned `isKeyBackendG_congrDel` as an
`∗-∗` (F7).

## Target 1: the committed statements

### What is good

- **The contract's new parameters are abstract**: `DP`, `SR`, `SRh` are defaulted parameters of
  `isKeyBackendG`/`batchTxSpecG` (`InvStore.lean:1053-1058, 1262-1267`). mvcc's assumed backend and
  its existing proofs are untouched, and `compactJobPreR_none` (`InvCompact.lean:189`) shows the old
  precondition is the assumed backend's instance. This is the "one general spec, special cases are
  instances" shape.
- **`rdCap2` is needed and correctly motivated.** `h.WriteKeyValue(keys[i], values[i])`
  (`kvstore_compaction.go:65`) reads two slices at once. `rdCap` lends one. Over bbolt both come
  from the fractional `txLive` (`InvBbolt.lean:113`), so two loans at once are provable.
- **Reading the slices across the batch's deletes is true of Go and of bbolt.**
  - The job reads `keys[i]`/`values[i]` only between `UnsafeRange` and `Unlock`
    (`kvstore_compaction.go:58-66`). After `Unlock` it uses only the value `rev` (line 87).
  - bbolt's `Bucket.Delete` (`bucket.go:499-533`) reads the key, and `node.del` (`node.go:145-159`)
    only rewrites the heap `inodes` slice. Page memory is untouched, and nothing remaps before
    `Commit`.
  - So the plan's §4 row "txBytes after Delete: *uncertain*" can be marked verified. Put the reason
    in `InvBbolt`'s docstring.
- **`thinV`, `dlReg`/`dlIs`, `safeStC`, `viOk`** (`DelKeys.lean`) are small, persistent where they
  should be, and say what their docstrings say. `safeStC_of` and `thinV_refl` are the right first
  laws.
- **`UnsafeSeqPut.specC`'s new premise is true of the code and needed by it.**
  - `baseReadTx.UnsafeRange` puts bbolt's keys before the buffer's, so buffered keys must lie above
    the committed ones.
  - mvcc's revisions are above every revision ever written, so `keyPutOk` (above the logical bucket,
    which contains the committed keys) discharges it.
- **The safe-range slot clause matches Go.** `LockForSafeRangeDelete` is `safeRangeDeleteMu.RLock()`
  (`backend.go:1115-1121`), held for the whole pass (`kvstore_compaction.go:31-32`). An exclusive
  `SR`/`SRh` pair handed from job to job is the right token.
- **The job's code meets O3's premise** (with the one-shot permits fixed, F4). In one session the job
  does at most `batchNum` deletes (the range returns at most `limit` keys, each deleted once,
  `kvstore_compaction.go:58-64`), plus one `Meta` put in the last batch. The session starts with
  `pend < P.limit` (`sessPuts`, `BackendBridge.lean:136-138`), and `ForceCommit` between batches
  resets the count. So `CompactionBatchLimit ≤ 2^56` (with `P.limit` bounded) gives `Unlock`'s
  `pend + hookMax < 2^58`.
  - A non-positive limit is already a filed Go bug (`issues/etcd-compaction-negative-batch-limit.md`:
    `unsafeRange` treats `limit ≤ 0` as unbounded and the loop never ends). The job already assumes
    a positive limit through `isStore`. The new premise belongs in the same place.

### Findings

**F1 (hard: sound/complete against the implementation). The limited range lends against `Locked l`,
which recurs in later sessions.** `InvStore.lean:1104-1109`: the post gives
`rdCap Rd (Locked l) ∗ rdCap2 Rd (Locked l)`.
- `rdCap` is persistent and `Locked : Puts → IProp` is one predicate for every session. With `l = []`
  (the job's case), every later session's `Locked []` claims the old slices are readable.
- Over bbolt the slices are `txBytes tx` of this session's transaction, readable only under its
  `txLive` (`InvBbolt.lean:124`), and the batch's `Unlock` commits it.
- So the bridge's `sorry` at `BackendBridge.lean:2327` is not provable for any choice of `Locked`.
  It would have to show `txBytes tx₀ s b ∗ Locked [] ⊢ s ↦* b` for a `Locked []` taken after
  `tx₀` closed.
- This is Draft 3.5's "read-only for good" in another form: "for every later holder of the lock".
- The point read (`InvStore.lean:1080-1084`) avoids it with a per-call `∃ T, T ∗ (T -∗ Locked l) ∗
  rdCap Rd T`. The bridge picks `T := bkLockedAt γ P b st l`, which is pinned to `st.tx`
  (`BackendBridge.lean:1870`).

*Callers affected*: the bridge (unprovable); the job (`store__scheduleCompaction.lean:342, 409-417,
492-500`), which would read through `T`.

*Restatement*: lend per call, and let the deletes run under the lent token.
- The range returns `∃ Rd T, T ∗ (T -∗ Locked l) ∗ rdCap Rd T ∗ rdCap2 Rd T ∗ pairVals Rd ks vs …`.
- It also returns the session's delete capability over the same `T` and `Rd`:
  `□ ∀ key k, {{ T ∗ Del k ∗ DP k ∗ □ Rd key k }} UnsafeDelete(Key, key) {{ T }}`.
- `T` must then stand for "this session, any later state" (`∃ st, bkLockedAt' γ P b st l ∗
  ⌜st.tx = tx₀⌝`, with deletes allowed), so that `T -∗ Locked l` still holds after the deletes.
- This also fixes F2: the delete clause is then the bridge's own, over its own `Rd`.

**F2 (hard: complete against the implementation). The delete clause takes a caller-chosen `Rd`.**
`InvStore.lean:1088-1095`: `∀ … (Rd : GoSlice → GoString → IProp GF), {{ … Locked l ∗ Del k ∗ DP
k ∗ rdCap Rd (Locked l) ∗ □ Rd key k }} UnsafeDelete … {{ Locked l }}`.
- For an abstract `Rd`, the bridge's only way to read `key` is `rdCap`, which consumes all of
  `Locked l` and returns it only in a wand.
- The backend's `UnsafeDelete.specC` needs `batchLocked` and the key's points-to at the same time
  (`batchTxBuffered__UnsafeDelete.lean:44-52` of the diff).
- So the `sorry` at `BackendBridge.lean:2324` is unprovable. This answers the author's question:
  the clause is strong enough for the job (whose step is now glue, `store__scheduleCompaction.lean:
  454`), but no backend can meet it.

*Restatement*: as in F1 (the delete capability returned by the range, over the range's `Rd`/`T`).
Or make the read predicate a parameter of the contract, `RdK`, shared by the range's `pairVals` and
the delete's `□ RdK key k`, so that the bridge knows what it means.

**F3 (hard: the assumptions check, §4, misses an unmet premise). bbolt's `Delete_kv` cannot take a
key from its own transaction.**
- `Spec/go_etcd_io/bbolt/Bucket__Delete_kv.lean:29-35` takes `ownWTxG tx … ∗ key ↦*{dk} kb`.
- `ownWTxG` holds `txLive tx 1` (`InvBbolt.lean:134`). A key that is `txBytes tx` (the job's
  `keys[i]`, from the write cursor, `batch_tx.go:194-226`) is readable only by lending all of
  `txLive tx 1`, which `Delete_kv` also needs.
- The §4 row "`Bucket.Delete_kv` … yes" holds only for an owned key slice: D22's and the lessor's
  deletes.
- The use is true of bbolt v1.5.0 (`bucket.go:518-532`: `c.seek(key)`, `bytes.Equal`, `node.del`
  reading `key`, writing only heap state).
- So the fix is a widened trust-boundary axiom, and the trust base grows: say so in the plan and
  in `etc/tcb-baseline.txt` when it lands.

*Callers affected*: `UnsafeDelete.specC` (its `key ↦*{dk} kb`), the bridge's delete clause.

*Restatement*:
- `Delete_kv`'s precondition takes `key ↦*{dk} kb ∨ txBytes tx key kb` (post: the same back).
- `UnsafeDelete.specC` takes `key ↦*{dk} kb ∨ rdB st.tx key kb` (the session's own transaction).

**F4 (hard: sound and faithful; the O3 budget does not bound). `bkDP gp k := ownToks gp 1` at a free
name.**
- **Unprovable.** `BackendBridge.lean:2118`, and the bridge takes `gp : GName` as a plain parameter
  (`:2283`). Its hypotheses are persistent and own nothing at `gp`. The range clause must produce
  `[∗list] DP p.1` (`InvStore.lean:1109`), and a fragment `◯ 1 : Auth Nat` cannot be made at a given
  name (only `ownToks_0`, `TokSet.lean:120`). So `:2327` is unprovable for that reason too.
- **Would not bound if minted.** Suppose the bridge's `Locked` carried a stock at `gp`. The clause
  still hands out a permit per returned key on *every* call, with `Locked l` returned unchanged, so
  a session can call the range repeatedly and collect unboundedly many permits.
  - In Go, deleting an absent key still increments `pending` (`batch_tx.go:229-246`, bbolt returns
    nil). The permits must bound calls, not keys.
- **The `Meta` put is unbudgeted.** The O3 "one `Meta`-put permit from `LockOutsideApply`" is not
  drafted. The `Meta` put clause (`InvStore.lean:1110-1117`) returns `Locked l` with `pend` one
  higher.

*Restatement*: put the budget in the session. Either:
- `LockOutsideApply`'s post gives `DPs N` (`N := 2^56`; the store's `isStore` premise
  `CompactionBatchLimit ≤ 2^56`), with `UnsafeDelete` and the `Meta` put each spending one; or
- O3's option (b): `Locked l n` counts the operations.

Either way `DP` loses its key argument (`bkDP gp _k` already ignores it).

**F5 (hard, follows from F1/F2; Draft notes claim otherwise). The new bridge's non-compaction clauses
are not "the old bridge's proofs".**
- `isKeyBackendG_of_backendC` chooses `Locked := bkLocked γ P b` (`BackendBridge.lean:2307`), whose
  `sessPuts` demands `st.ndel = W64 0` (`:137`).
- `UnsafeDelete` increments `ndel` (`BatchLemmas.lean:202-236`), so the delete clause's post
  `Locked l` cannot be `bkLocked l`.
- The job's `Unlock` after deletes uses the no-puts clause `{{ Locked [] ∗ W ∗ P }}`
  (`InvStore.lean:1069-1070`). That clause must then go through `Unlock.specC`'s deleting branch,
  with the deleted keys' `dlIs` carried in `Locked`.
- So a new `Locked` is needed and every clause over it is re-proved (`bkLocked` has 54 uses, plan
  3.3). The "four new cases" and the plan's "Draft round 2" estimate understate this.

*Restatement*: record in the plan that the bridge's `Locked` changes, and that §3.3's sketch
(`pend ≤ l.length + ndel + extra`) needs F4's stock to bound anything.

**F6 (hard: sound; plan O2). `dlNone` is linked to nothing.**
- `dlNone γ := dghostVar γ.dln (DFrac.own 1) true` (`DelKeys.lean:78`): the whole fraction, the
  creator's (`dlInit`, `:83`). After `dlReg_fix` it "stays the creator's" (`:88-96`).
- No invariant holds a share. `UnsafeDelete.specC` neither consumes nor checks it (`grep dlNone`:
  only `DelKeys`, `InvNew`, `NewAlloc`, `InvBackend`).
- So the law its docstring promises (`thinV … vd L → vd = L`) is false of reachable states. Once the
  registration is fixed and the job deletes, the creator still holds `dlNone`.

*Callers affected*: every D22 exact reader (see Target 2, D22 map).

*Restatement*, either:
- **(a) Link it.** A one-shot whose pending half is in `batchGhostAt` (and so readable in `rtRest`'s
  rule), with `UnsafeDelete.specC` of a safe-range bucket requiring the persistent "shot" witness.
  The rule "pending → physical = logical" goes in the quarters. `dlNone` becomes a fraction of
  "pending", if D22's exact readers can be concurrent.
- **(b) Simpler: drop `dlNone` and `BNames.dln`.** Take exactness from the unfixed registration.
  `savedPredOwn γ.dlg (DFrac.own 1) _ ∗ dlReg γ Φ ⊢ False` without a later
  (`saved_pred_valid_2`, `SavedProp.lean:281`, gives `⌜✓ (own 1 • discard)⌝`), so `dlIs` is false
  and `thinV` is exact while the registration is unfixed.
  - The server's boot routes `dlInit` either to the store, which fixes it (the compactor on, M2:
    "only the server configuration that never installs a snapshot", `m2:notes/m2-plan.md:251-253`),
    or to the exact readers (D22).
  - It is exclusive: `own q • discard` is valid for `q < 1`, so only the whole registration excludes
    deletions. That is enough if D22's exact reads are sequential (uncertain; see Target 2).

**F7 (preference "every premise has a source"; affects the planned wiring). Who fixes the predicate,
and the `▷`.**
- **The author's question: yes.** `dlInit` goes to whoever calls `newBackend`/`New`
  (`InvNew.lean:64, 161`): the server's boot and D22's `SnapApplyWalk`, both of which currently
  discard it with `-` (`BootBackend.lean:87`, `SnapApplyWalk.lean:284`). Any holder can fix `Φ` to
  anything.
- **Sound regardless.** The backend's statements are relative to `Φ`, and a `Φ` covering non-Key
  buckets only weakens what readers learn about buckets nobody thins.
- **But mvcc can use the backend's thinness only for `Φ ≡ delKey`.** The wiring must hand `dlInit`
  to `NewStore` (or to whoever builds the store's `storeBackend`) unfixed. The discarding `-` in
  `SnapApplyWalk` means a backend opened by a snapshot can never be compacted, nor (under F6(b))
  read exactly. Keep it, not drop it.
- **`isKeyBackendG_congrDel : □(∀k, Del k ∗-∗ Del' k)` (plan §2) is not provable for
  `bkDel`/`delKey`.**
  - `saved_pred_agree` gives only `▷ (Φ x ≡ Ψ x)` (`SavedProp.lean:287`), so `bkDel k ⊢ ▷ delKey γ k`.
  - mvcc's readers use `Del k` directly (`iunfold mvcc.delKey at Hdel; icases`,
    `storeTxnCommon__rangeKeys.lean:729-731`).
  - `delKey` is ownership of persistent ghost fragments plus pure facts, so it is presumably
    timeless and the `▷` can be stripped inside a WP (uncertain: I did not check the
    `Timeless` instances of `crevLb`/`idxCert`).

  *Restatement*: instantiate the store's `Del` as `fun k => ▷ delKey γ k`, or state the
  congruence as `Del k -∗ ◇ Del' k`, and strip at the readers. Or O1's fallback (c).

**F8 (hard: sound, likely; plan 3.2). `Unlock.specC`'s deleting branch says nothing of the write
buffer.**
- Branch 2 (`batchTxBuffered__Unlock.lean`, diff lines 63-65) is `thinV γ (sData P st.S) (vData P
  (st.C, st.R)) ∗ W ∗ Pk ∗ Q`.
- The first branch's `viewSame` (`Model2.lean:280-282`) also requires the buffer's non-hook buckets
  to be empty, because `Unlock` writes the buffer back into `readTx.buf` (`batch_tx.go:356-360`)
  before committing.
- A session that puts and then deletes the same non-hook key keeps the put in `W` while `S` lacks
  the key. `thinV` holds, but readers between the write-back's `readTx.Unlock()` and the commit's
  `readTx.Lock()` (`:376-381`) see the key, which is in neither view.
- The job puts only into `Meta` (a hook bucket under `bridgeParams`), so the conjunct costs it
  nothing.
- *Uncertain*: whether the backend's invariant already rules this session shape out.

*Restatement*: branch 2 takes `⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i =
[]⌝`. Branch 1 is then the instance `thinV_refl` of branch 2. Drop it ("no disjunction of
alternative specs", "after a change, drop what existed only for it").

**F9 (preference "API, not implementation"; measures: coupling, duplication).**
- `kbSR` (`InvStore.lean:1419-1422`) and `srSlot` (`BackendBridge.lean:2122`) define the same
  resource twice.
- mvcc's `InvStore` names the backend's private field (`backend.bF go!"safeRangeDeleteMu" d.be`).

*Restatement*: one `backend.srSlot γ b` in the backend's API (next to `wbTok`), used by both.

**F10 (hard: complete; O4). `kbWTSupply` is not derivable from `srvWTPool` as stated.**
- `kbWTSupply (some d) := □ (⧗ 1 ={⊤}=∗ wbTok d.γB)` (`InvStore.lean:1428-1431`).
- `srvWTPool`'s takers must agree on the pool's current backend through a share of `E.γbe`
  (`srvWTPool_take_at_d`, `InvApplier.lean:950-953`).
- The pool's backend changes at `applySnapshot` (`InvApplier.lean:811-814`). A persistent supply
  for a fixed `d` is therefore false in general, and the job holds no share of `E.γbe`.
- The mechanism (a receipt per take, each Go step giving `⧗ 1`, `PostLifting.lean:376-381`) does
  fit the job's loop.

*Restatement*: either give the job a share of `E.γbe` (D22's split changes: ask its owner, as O4
says), or state the supply as "a token of the current backend" with the job's agreement through
the store's `kb`. Valid only in the no-snapshot configuration, where `d` never changes; that is a
fact the server must state.

**F11 (measure: caller burden).**
- `newPost`/`newPostK` grew a positional conjunct, and both destructurers changed
  (`BootBackend.lean:87`, `SnapApplyWalk.lean:284`). The Local rule's cautionary example is "the
  boot contract accreted a clause per stage". `dlInit` is the backend's own footprint, so the
  conjunct is right, but callers should take it by a named law, not position.
- The job's glue drops the permit list (`store__scheduleCompaction.lean:342`, `-`). With F4's
  per-session stock it needs no list indexing.

## Target 2: the thin-view design (plan 3.2, not yet written)

### Soundness against Go: readers never look up compacted keys

| Client of the `Key` bucket (`γ.view`) | Verdict |
|---|---|
| mvcc's readers (`storeTxnCommon.rangeKeys`, `kvstore_txn.go:85-140`) | **Verified.** They read revisions the index gives at `rev ≥ compactMainRev` (checked under `s.mu.RLock`, `kvstore_txn.go:46-62, 91-93`), which are kept. The proof already discharges the `Del` disjunct (`storeTxnCommon__rangeKeys.lean:727-739`, `rangeAnswers_not_del`). A miss would be `lg.Fatal`, so the proof is what excludes it. |
| mvcc's write transactions (point reads under the batch lock) | **Verified.** The same `rangeKeys`; the point-read clause already has the `Del k` disjunct (`InvStore.lean:1080-1084`). |
| watchers (`rangeEvents`) | Out of scope: their proof uses `snapThin_frozen` (`rangeEvents.lean:66-68`), the "no compactor" fact. |
| `store.restore`/`Restore` | **Verified.** Over a fresh or received backend (`kbNoCmp`, `store__restore.lean:599-600`); unaffected. |
| lessor, auth, membership, cindex, storage version | **Verified.** Not clients of `γ.view` (`grep bView`: no such file); they read `Lease`/`Meta`/auth buckets through `rbOwn`/the hook. Compaction deletes only `Key`, the only safe-range bucket. |
| the hash (`HashByRev`) | Not specified in this repository (no spec file); unaffected. |
| defrag | Out of scope (its slot only). |
| snapshot sender (`backend.Snapshot`) | Exact under O2. M2's configuration installs and sends no snapshot (single member, `m2:notes/m2-plan.md:251-253`). |

So the thin view is sound for every verified client. It is also the strongest true statement here:
Go guarantees exactness except for deleted keys.

### Other points of the design

- **Good: logical `L` in `γ.view`, physical thin of it**, with the writer's third branch keeping
  soft-deleted safe-range entries in `L` (`relog`). This matches mvcc's own model, "the logical
  bucket the view holds is not changed" (`InvStore.lean:1022-1026`). Thinness is checked at `RLock`
  against the reader's own `bView γ q L`, which keeps `L` fixed for the reader, as the exact design
  does now.
- **D22's exactness needs a link that 3.2 does not draw** (F6). As drafted, the quarters hold
  `ghostVar γ.view _ L ∗ thinV P γ rv L` and nothing ties `dlNone` to them. Add either the one-shot
  rule to `batchGhostAt`/`rtRest`, or (simpler, F6(b)) derive exactness from the unfixed
  registration and drop `dlNone`.
- **D22 statements that need an exact view**, and what each would hold:

  | Statement | Uses | Exact through |
  |---|---|---|
  | `backend.Snapshot.spec`'s `Q (sData P D) …` against `viewAt γ vd` (`Spec/…/backend__Snapshot.lean:54`) | the snapshot sender: `SnapSendBranch.lean:59, 209`, `InvSnapSend`, `mvcc/Image.lean` | `dlNone` (or the unfixed registration) of the *running* backend; with the compactor on there is no sender |
  | `bViewC … true`, `keyCleanRead`, `keyReadSnapC`, `rbClean` (R5a/R5c) | `store__Restore.lean:51-52, 126-127`, `RestoreMoves.lean:572-600`, `SnapApplyWalk` | the *new* backend's `dlInit`, which `SnapApplyWalk.lean:284` now discards: keep it |
  | newPost's `bView` over an image | `InvImage.lean:192`, `mvcc/Image.lean:56` | the new backend's `dlInit` |
  | the boot backend's clean view and `kbNoCmp` | `BootBackend.lean`, `NewStore.lean:91`, `BuildLemmas.lean:110` | before any delete; `dlInit` routed to the store or kept, by configuration |

  `dlNone`/`dlInit` is sufficient for all of these, provided it is linked (F6), it is kept rather
  than discarded at `SnapApplyWalk`/`BootBackend`, and D22's exact reads are not concurrent with each
  other. The last is uncertain: `own 1` is exclusive, and I did not check whether the sender's
  `Snapshot` call can overlap a restore's clean read on the same backend.
- **`cacheValidC`'s parameter `L` (`DelKeys.lean:115-119`) is "the current logical view".** A
  writer's third branch changes `L` (an overwrite in a non-safe-range bucket, `Lease` or the auth
  buckets, is in `vData`). The relation is then stated against an `L` that moved, and every cached
  entry must be re-proved or invalidated. This is the place where the plan's finding (iii) and the
  write-back's version bump meet. *Uncertain*: whether `histAt`/`cachedAt`'s versions already
  invalidate the old entries. Settle it before re-threading `ReadSide` (753 lines) and
  `ConcurrentReadTx`.
- **The `▷` (plan 3.2's own *uncertain*) is real** (F7): it reaches mvcc's readers, not only the
  backend's `RLock`. O1's option (c) avoids it; with option (b), mvcc's `Del` takes the `▷`.
- **"Every backend read spec from exact to thin"** is the right direction, and the margin is known
  (exact under the unfixed registration or `dlNone`). Make the exact case an instance, a law
  `thinV_exact` from the exactness token, not a second family of read specs (the "one general spec"
  preference): the `…C` clean-read family (`keyCleanRead`, `keyReadSnapC`) should become thin reads
  plus that law.
- **Budgets.** O3 holds of the Go loop once restated (F4). O4's mechanism fits but needs the
  backend agreement (F10). The safe-range slot is right but nothing mints it yet (`newBackend`
  returns no `srSlot`, plan 3.4, still to do).

## Ranking (most need of revision first)

1. **mvcc's contract clauses for the job** (`InvStore.lean:1088-1109`: the range's lending, the
   delete's `Rd`, `DP`) with **`bkDP`**: F1, F2, F4, F5. Unprovable as stated. Restate before the
   backend's invariants are re-threaded, because the re-threading proves exactly these.
2. **`dlNone`/`dlInit` and the exactness design** (F6, F7, the D22 map): an unlinked token, and a
   law that would be false. Decide F6(a) or (b) now; (b) removes a `BNames` field and a token.
3. **`UnsafeDelete.specC` and bbolt's `Delete_kv`** (F3): an unmet trust-boundary premise. A small,
   true widening of the axiom, but a trust-base change to record.
4. **`compactJobRes`/`kbWTSupply`/`kbSR`** (F9, F10): derivability from D22's pool, and duplication.
5. **`Unlock.specC`** (F8): one conjunct, and drop branch 1.
6. **The thin-view design (Target 2)**: sound against Go for every client in scope. Settle
   `cacheValidC`'s `L` and the `▷` before writing.
7. **`thinV`, `dlReg`/`dlIs`, `safeStC`, `viOk`, `UnsafeSeqPut.specC`, `BNames`' fields**: fine as
   they are.

## Verified vs uncertain

**Verified** (code read):
- bbolt `Delete` keeps cursor slices valid within the transaction.
- The job reads slices only before `Unlock`.
- At most `batchNum` deletes per session.
- mvcc's readers discharge `Del`.
- Only `Key` is thinned, and no non-mvcc client reads `γ.view`.
- `ownToks` cannot be minted at a given name.
- `sessPuts` excludes deletes.
- `dlNone` is referenced nowhere else.
- `saved_pred_valid_2` gives validity without a later and agreement under one.
- The pool's take needs `E.γbe`.
- The M2 configuration excludes snapshots.

**Uncertain**:
- F8: whether the invariant already excludes put-then-delete sessions.
- Whether `delKey` is timeless (F7).
- Whether D22's exact reads are sequential (F6(b), the D22 map).
- `cacheValidC`'s invalidation (Target 2).

**No new Go bug.** The negative batch limit is already `issues/etcd-compaction-negative-batch-limit.md`.
