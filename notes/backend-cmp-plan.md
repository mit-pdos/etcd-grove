# backend-cmp: compaction over the real backend (Scope, 2026-10-28; for the user's approval)

The stage M2 waits for (`m2` branch, `notes/m2-plan.md` there, "Review round 3, and M2 paused"):
etcd's real backend supports what mvcc's compaction needs, so that the bridge
`isKeyBackendG_of_backend` (`Proof/.../storage/mvcc/BackendBridge.lean:2128`) is proved with `Cmp`
true and `storeCmp γ` (`kbCmp kb := kb = none`, `InvStore.lean:1502`) holds of the real backend.
The gaps are `notes/decisions.md:4841` ("The compaction over the real backend"): three named in the
task, and a fourth the entry lists (budgets and slots), which is in scope too: without it the job
is still unprovable. Paths below are under `Proof/go_etcd_io/etcd/server/v3/storage/` (`P:`) and
`Spec/go_etcd_io/etcd/server/v3/storage/` (`S:`); Go under `.lake/go-src/etcd/server/storage/`.

## 1. The configuration

**In**: exactly the backend calls of mvcc's compaction, and what concurrent readers see of them.
- The job, `scheduleCompaction` (`mvcc/kvstore_compaction.go:28-110`): `LockForSafeRangeDelete`/
  `UnlockForSafeRangeDelete` (once per pass), per batch `BatchTx().LockOutsideApply()`,
  `UnsafeRange(Key, last, end, batchNum)` (`backend/batch_tx.go:194,206`: bbolt's writer cursor),
  `UnsafeDelete(Key, keys[i])` (`batch_tx.go:229`, `:418` counts `pendingDeleteOperations`),
  `UnsafeSetFinishedCompact` = `UnsafePut(Meta, finishedCompactRev, revBytes)` (`mvcc/store.go:56`)
  in the last batch, `Unlock` (`batch_tx.go:328`: write-back, then a commit since a delete is
  pending), `ForceCommit` between batches, `Size`/`SizeInUse` (proved).
- `store.Compact`'s synchronous part (`mvcc/kvstore.go:197-232`): `SetScheduledCompact`
  (`store.go:38`: `LockInsideApply`, `UnsafePut(Meta, scheduledCompactRev)`, `Unlock`),
  `ForceCommit`, and `checkPrevCompactionCompleted` (`ReadTx`, `RLock`, two `UnsafeRange(Meta, k,
  nil, 0)`, `RUnlock`).
- The readers concurrent with it: `ConcurrentReadTx`/`ReadTx` and their `RLock`/`UnsafeRange`,
  the apply thread's write sessions (already proved; their statements change, section 3.2).

**Out** (each stays as `lean` has it; a statement that needs it says so by premise or token):
- defragmentation (the writer of `safeRangeDeleteMu`; its slot is all we model);
- Restore, snapshot send and snapshot apply on a compacting server (M2's `NewServer` premise:
  compactor on only in the no-snapshot configuration, `notes/m2-plan.md` round 1); so the D22
  statements keep exact views (section 5) and none needs a thin one;
- reopening a backend over a compacted file (`bkNoCmp`, `InvStore.lean:466`, stays a fact of
  fresh or received data);
- watchers (M2's "no compactor" fact), the hash (`h.Hash`, `s.hashes.Store`: mvcc's side, unchanged);
- the `Lease` bucket's delete (D22/T3, `rbDel`): a real, view-changing delete; unchanged.

## 2. The top-level statement

Now (`BackendBridge.lean:2128-2160`, abridged): for 22 callee specs, `bridgeParams P`, any `Del`
and **`(Cmp : Prop) (hC : ¬ Cmp)`**,
```
isPkgInit backend ∗ isPkgInit schema ∗ isBackend γ P W Pk b ∗ keySized γ P b ⊢
  isKeyBackendG (…#b) (bkView γ) (bkRTx γ P b) (wbTok γ) keyPutOk Del W W iprop(True) Cmp Pk
    (bkHookIs γ) (bkReq γ P b) (fun r => rbOwn γ r ∗ ⌜leaseParams P⌝) (bkBt b)
```
Draft (new callee specs: `UnsafePut`, `LockForSafeRangeDelete`, `UnlockForSafeRangeDelete`;
`Del` no longer free: the backend's registered deletable keys, 3.2):
```
theorem isKeyBackendG_of_backend (…25 specs…) {P} (hP : bridgeParams P) (hV : metaVI P) (γ W Pk b) :
  isPkgInit backend ∗ isPkgInit schema ∗ isBackend γ P W Pk b ∗ keySized γ P b ⊢
  isKeyBackendG (…#b) (bkView γ) (bkRTx γ P b) (wbTok γ) keyPutOk (bkDel γ) W W iprop(True)
    True Pk (bkHookIs γ) (bkReq γ P b) (…) (bkBt b) (SR := srSlot γ b)
-- bkDel γ k := dlIs γ (keyName, k)   (3.2);  metaVI P : P.VI enforces metaRevVal at the compaction keys (3.3)
```
For mvcc: `kbCmp kb := True` (`storeCmp γ` then holds of both instances: the compaction specs'
premise becomes trivially dischargeable; dropping the `Cmp` parameter is a later cleanup, decision
O5). `storeBackend_of_backend` (`StoreBackend.lean`) gets `Del := delKey γ` from `bkDel` through the
store's registration (`storeRegd s γ`, `InvStore.lean:2026`, as `lateW` gives `W`): a lemma
`isKeyBackendG_congrDel : □(∀k, Del k ∗-∗ Del' k) → isKeyBackendG … Del … ⊢ … Del' …`. Then
`compactJobPre` (`P:mvcc/InvCompact.lean:170`) loses `⌜storeCmp γ⌝` and, because of 3.4, stops
being persistent.

## 3. The layers that change, drafted

### 3.1 Deletion from the safe-range `Key` bucket

Now: `S:backend/batchTxBuffered__UnsafeDelete.lean` premise `P.SB bi.name = false`; `safeSt`
(`P:backend/Model2.lean:249`) has a third clause "every committed key of a safe-range bucket is in
the writer's contents" (`bktOf st.C n` ⊆ `bktOf st.S n`), which `UnsafePut`'s/`UnsafeSeqPut`'s
SB premise (`kb` above every key of `st.S`) turns into clause 2 (committed keys below the write
buffer's). `BParams.SB`'s docstring (`Model2.lean:40`) says "never deleted from".

Draft:
```
def safeSt P st := safeRv P (st.C, st.R) ∧ ∀ n i, BT n = some i → SB n →
    ∀ kc vc e, (bktOf st.C n).lookup kc = some vc → e ∈ bkOf st.W.bks i → strLt kc e.1   -- clause 3 gone
UnsafePut/UnsafeSeqPut premise:  P.SB bi.name → ∀ kc vc,
    ((bktOf st.S bi.name).lookup kc = some vc ∨ (bktOf st.C bi.name).lookup kc = some vc) → strLt kc kb
UnsafeDelete: P.SB bi.name = false  ⟶  (P.SB bi.name → □ dlIs γ (bi.name, kb))   -- the deletion registered (3.2)
```
The bridge discharges the new put premise from `keyPutOk` (above the logical bucket `m`, which
contains the committed keys by the thin relation of 3.2). Touches: `safeSt` 16 uses in 5 files
(`WritebackLemmas`, `BatchLemmas` (`safeSt_put`, `safeSt_S_nonSB`), `CommitLemmas:279`, the bridge);
the put specs' callers: 13 files; `UnsafeDelete.spec`: 9 files (the D22 ones, `applySnapshot`,
`SnapApplyWalk`, `BuildLemmas`, `NewServer`, delete only non-SB buckets: their premise discharge
changes from `SB = false` to the vacuous implication).

### 3.2 The readers' view: exact up to registered deletable keys

Now: `γ.view` is a `ghostVar` of the physical view `vData P rv` (`Model2.lean:172`): half the
clients' (`bView`, `P:backend/InvBackend.lean:184-194`), a quarter the batch lock's
(`batchGhostAt`, `:530`), a quarter `readTx.mu`'s (`rtRest`, `:466`). Changing it needs all of it:
`batchTxBuffered.Unlock.spec` (`S:backend/batchTxBuffered__Unlock.lean`) either `viewSame P st`
(`Model2.lean:280`: the writer's contents read as the view off the hook's buckets) or the clients'
whole `bView γ 1 vd`, returned at `sData P st.S`. The job's sessions change the view (their commit
removes keys) and hold no clients' share (half is under `s.revMu`). `cacheValid` (`InvBackend:412`)
says a cached read buffer reads, with the current committed data, *exactly* as the current state.

Draft: `γ.view` holds the **logical** view `L`; the physical states are thin of it.
```
-- the deletable keys: a predicate the backend's creator registers (decision O1, option b)
BNames.dlp : GName;  dlReg γ Φ := savedPredOwn γ.dlp DFrac.discard Φ   -- Φ : GoString×GoString → IProp, persistent
dlIs γ nk := ∃ Φ, dlReg γ Φ ∗ □ Φ nk
thinV P γ (rv : RView) (L : VData) : IProp :=      -- persistent
  ⌜∀ nk v, vData P rv nk = some v → L nk = some v⌝ ∗ □ ∀ nk, ⌜L nk ≠ none ∧ vData P rv nk = none⌝ -∗ dlIs γ nk
rtRest / batchGhostAt:  ghostVar γ.view _ L ∗ thinV P γ rv L            (was: ghostVar γ.view _ (vData P rv))
viewSoft P st L : the session put nothing off the hook's buckets and sData P st.S is thin of L (deletes only)
Unlock.spec pre:  (⌜viewSame P st⌝ ∗ W ∗ Pk ∗ Q)
               ∨ (viewSoftG γ P st ∗ W ∗ Pk ∗ Q)                        -- new: no clients' share
               ∨ (∃ L, bView γ 1 L ∗ Pk ∗ (bView γ 1 (relog P st.S L) -∗ W ∗ Q))
-- relog P S L := sData P S with L's SB entries missing from S kept (soft deletes stay in the logical view)
cacheValid:  ⌜vData P (rv.1, rv'.2) = vData P rv⌝  ⟶  thinV P γ (rv.1, rv'.2) L     (L the current logical view)
```
What each reader then gets: `readTx`/`concurrentReadTx` `RLock` posts give `rv` with `thinV P γ rv L`
against the clients' `bView γ q L` (was: `vData P rv = L` by agreement); the bridge's `keyReadSnap`
gives `snapThin m m' (bkDel γ)` instead of `snapThin_refl` (3 uses); the batch transaction's point
read uses the existing `Del k` disjunct of `batchTxSpecG` (`InvStore.lean:1065-1075`). A put session
keeps the third branch: mvcc's apply thread is unchanged (`bkView γB q m := ∃ vd, bView γB q vd ∗
keyView vd m`, `InvStore.lean:1346`, keeps its text; `m` is now the logical bucket, as mvcc's own
model already has it: "the logical bucket the view holds is not changed", `InvStore.lean:1022-1026`).

**Exactness for D22** (decision O2): a fresh backend's clients get `bViewC … true` (R5a); add
`dlNone γ` (exclusive, from `newPost`) whose holder knows `vData P rv = L` (no registered deletion
happened); `UnsafeDelete` of an SB bucket consumes it into the persistent `dlOn γ`. `keyCleanRead`/
`keyReadSnapC`, `backend.Snapshot`'s post (`S:backend/backend__Snapshot.lean`: `Q (sData P D) …`
against `viewAt γ vd`) and `rbClean` stay exact under `dlNone`; thin otherwise.

Touches: `bView` 61 uses in 27 files (most unchanged in text: the meaning moves); `rtCore`/`rtRest`
28 uses / 8 files; `cacheValid` 17/4 (its proof in the commit path, `CommitLemmas`, `ReadSide` 753
lines, `backend__ConcurrentReadTx` 260: **the real work**); `viewSame` 20 uses (12 in the bridge);
`batchTxBuffered.Unlock.spec` 9 files; RLock specs 10 files; `newBackend`/`New` 3+2 files (`Φ`);
`viewAt` 7/4.
*Uncertain*: `savedPredOwn`'s agreement is under `▷` (Perennial `Ghost/SavedProp.lean`): the
readers strip it at `RLock`'s step; if that does not fit, decision O1's option (c).

### 3.3 The `Meta` keys

Now: under `bridgeParams` (`BackendBridge.lean:100`) `Meta` is a hook bucket (`HB`), which `vData`
omits: a read promises nothing, so `metaReadTx` (`InvStore.lean:622`: `metaReadSpec`, a value with
`metaRevVal`, `:581`) is unprovable; and `bkLocked` (the bridge's `Locked`, 54 uses) ties the
session's pending count to `Key`'s puts alone. (The third sub-gap of 2026-10-13, "the key must be
absent from the write buffer", is gone: `UnsafePut` allows a key put twice since etcd-io/etcd#21987,
`S:backend/batchTxBuffered__UnsafePut.lean:33-36`.)

Draft: a pure value invariant in the parameters, enforced at every write.
```
structure BParams := … VI : GoString → GoString → GoString → Prop      -- (bucket, key, value)
viOk P (D : Data) (R : RBuf) (W : WBuf) : every entry (n,k,v) of D, R, W has P.VI n k v
sessWf P st  += viOk P st.S st.R st.W ∧ viOk P st.C ∅ ∅
UnsafePut/SeqPut premise += P.VI bi.name kb vb;  hookStep P st st' keeps viOk (the hook's puts: P.VI holds of them)
readTx.UnsafeRange post  += every returned entry has P.VI          -- from rtCore's pure facts
metaVI P := ∀ k v, P.VI metaName k v ↔ (metaCompactKey k → metaRevVal v)   -- mvcc's instance
bkLocked γ P b l := ∃ st, batchLocked γ P b st ∗ … ∗ ⌜sint.Z st.pend ≤ l.length + st.ndel + extra st⌝   -- (O3)
```
Touches: `BParams` (3 literal sites), `hookStep` 26 uses / 11 files (the server's hook proofs in
`etcdserver/` must show `VI` of the consistent index and term: `VI` is trivially true off the
compaction keys), `sessWf`'s users, `readTx.UnsafeRange.spec` callers; `metaRevVal` 5 uses, 1 file.

### 3.4 Budgets and slots (the fourth gap)

Now: `compactJobPre` is persistent (`InvCompact.lean:170`), yet each batch spends `RT` (a reader slot
and an open share, `kbRT`, `InvStore.lean:1381`) for `LockOutsideApply`, `WT` = `wbTok` for its
`Unlock` and for its `ForceCommit` (unboundedly many batches); `LockForSafeRangeDelete.spec` needs a
`safeRangeDeleteMu` reader slot (`sync.ownRWMutex …`), which `isBackend` (`InvBackend:652`) does not
hold and `newBackend` does not give; `isKeyBackendG`'s clause takes `True` (`InvStore.lean:1265`).

Draft: `isKeyBackendG` gains `SR : IProp` (`{{SR}} LockFor… {{SRh}}`, `{{SRh}} UnlockFor… {{SR}}`;
`True` for mvcc's assumed backend); `newBackend` (or `New`) returns `isRWMutex safeRangeDeleteMu`
and one slot (`srSlot γ b`); the store keeps it in the tracked FIFO chain (`schedule.Scheduler.
Schedule.spec`: a job's `Pre`, and `Prev`/`Post` handed job to job), as the job's own resource. The
write-back tokens: decision O4.

### 3.5 mvcc's contract: the limited range's slices

Now: `batchTxSpecG`'s limited range (`InvStore.lean:1081-1092`) returns `pairVals (s ↦*□ b)`:
read-only *for good* (`decisions.md:4889`: "revisit with the backend's support"). False over bbolt:
its slices are `txBytes tx s b`, readable only while the write transaction lives
(`P:backend/InvBbolt.lean:124`, `txBytes_acc`), and the job's `Unlock` commits it. Draft: as the point read,
`∃ Rd T, T ∗ (T -∗ Locked l) ∗ rdCap Rd T`, readable across the batch's `UnsafeDelete`s (the delete
clause takes and returns `T`, or `rdCap Rd (Locked l)`: decision O3). Go reads `keys[i]`/`values[i]`
only before the batch's `Unlock` (`kvstore_compaction.go:58-66`): true of the code. Re-proves the
job (`P:mvcc/store__scheduleCompaction.lean`, 729 lines).

## 4. The assumptions check (what the new statements rest on)

| callee | assumes | holds in the new use? |
|---|---|---|
| bbolt `Bucket.Delete_kv` (`Spec/go_etcd_io/bbolt/`) | `G n = g`, `S.lookup n = some m` (bucket exists, current handle) | yes: `batchTx.UnsafeDelete` re-fetches the handle; `Key` exists after `NewStore` (as for `Lease`, proved) |
| bbolt `Bucket.Cursor_kvw`, `Cursor.Seek/Next_kv` | the write tx's ownership back only with the cursor; slices `txBytes` (persistent, read under `txLive`) | yes: `unsafeRange` finishes before the deletes; **no** for mvcc's "read-only for good" slices (3.5) |
| bbolt `txBytes` after `Delete` | (axiom: persistent, readable while live) | yes: bbolt removes the inode, the page stays mapped until `Commit`; *uncertain*, worth one line in `InvBbolt`'s docstring |
| bbolt `Tx.Commit_kv` | `ownWTx tx γ D S`; nothing about deletes | yes |
| backend `Unlock.spec` | `st.cnt.hw = false`, `pend + hookMax < 2^58` | needs the job's ops bounded: `pend ≤ limit + 1` with `CompactionBatchLimit ≤ 2^56` (a scope premise, O3) |
| backend `LockOutsideApply.spec` | `bOpen γ qo` | yes, inside `RT`, if the job owns an `RT` (3.4) |
| backend `ForceCommit.spec` | `wbTok γ`, `commitReq` / `bkReq` | `Req True True` is the plain wand: yes; `wbTok`: O4 |
| backend `LockForSafeRangeDelete.spec` | a reader slot of `safeRangeDeleteMu` | **no**: nothing mints it today (3.4) |
| backend `readTx.UnsafeRange.spec` on `Meta` | `limit ≤ 1` or a safe-range bucket | yes (`nil` end key) but promises no value: 3.3 |
| mvcc's job/compaction specs | `storeCmp γ` (premise of `Compact`, `updateCompactRev`, `compactLockfree`, `checkPrevCompactionCompleted`, `compactJobPre`) | becomes trivial (`kbCmp := True`) |
| mvcc `delKey` (`InvStore.lean:1755`) | on `lean`: `NoDelPutAt`; on `m2`: dropped (#22377) | the backend is agnostic (`Φ` is a parameter); the stage builds on `lean`, rebase M2 after |
| the server's hook (`hookStep`, `Pk`) | changes only hook buckets and `HK` keys | must now also keep `VI` (3.3): true (writes `consistent_index`/`term`) |

**Flags like M2's miss**: (i) mvcc's limited range promises persistent slices, a premise of the
job's proof false of bbolt (3.5); (ii) `compactJobPre` is persistent, so the job's proof assumes the
compaction costs no tokens, false of the real backend (3.4); (iii) `cacheValid` (exact) is false
once a commit soft-deletes a key the cached read buffer still holds (a tombstone put and compacted
in one commit interval): readers may then *see* a deleted key, harmless under the thin view but a
statement change. No Go bug found (nothing for `issues/`).

## 5. Overlap with D22 (the collaborator's; mapped, not changed)

- **R5a's clean read** (`bViewC … true`, `keyCleanRead`, `keyReadSnapC`, `rbClean`, `restore-plan.md:226`;
  10 files) and `store.restore`/`store.Restore` over a new backend (`storeBackendT_of_backend`,
  `kbNoCmp`, `RestorePre`, `SnapApplyWalk`): rest on the view being exact. With 3.2 they need
  `dlNone γ` next to `bViewC … true`; `newPost` gives both, so it is **additive** (the open's post
  and S8's item 7 thread one more token).
- **The snapshot sender** (D22 S-h, `InvSnapSend`, `SnapSendBranch`, `mvcc/Image.lean`) uses
  `backend.Snapshot.spec`'s exact `Q (sData P D)`: kept under `dlNone`; on a compacting server the
  image would be thin of the logical view (out of scope: no snapshots with the compactor on).
- **S8's swap** (`snapshot-s8-plan.md` items 6, 9, 13, 14): the new backend's write-back tokens
  (`srvWTPool`, `InvApplier.lean:815`, `receiptBound`) and its batch lock: O4's choice decides
  whether the job draws from the same pool; S8 must then move the job's share to the new backend
  too (only if compaction and restore are ever on together).
- `viewSame` in `etcdserver/InvStorageVersion.lean` and `SetTxPostLockInsideApplyHook`: unchanged
  (the first branch of `Unlock` stays); `hookStep`'s new `VI` conjunct reaches the hook's proofs
  (D22's stored-index window, `bkReq`), a one-line obligation each.

## 6. Open decisions, and the estimate

- **O1, how the backend knows the deletable keys.** (a) a parameter `Dl` of `isBackend` (129 files,
  60 specs: mechanical but large); (b) a saved predicate fixed at `newBackend` (`BNames.dlp`; callers
  of `newBackend`/`New`, 3+2 files, choose `Φ` = mvcc's late-bound `delKey`, as `lateW`); (c) a pure
  monotone set `γ.dk` whose authority mvcc keeps in an invariant with `delKey` of each member (no
  later, but mvcc's readers open that invariant). **Recommend (b)**, (c) if the `▷` does not fit.
- **O2, exactness for D22**: (a) the token `dlNone` (additive); (b) a third value of the `cln` flag;
  (c) no exactness (D22's clean reads become thin: rewrites their restore). **Recommend (a).**
- **O3, counting the job's operations** (`pend < 2^58`): (a) the limited range hands out a one-shot
  delete permit per returned key and `LockOutsideApply` one `Meta`-put permit, `Locked`'s index
  unchanged; (b) `Locked : Puts → Nat → IProp` (mvcc-wide re-threading). Either needs
  `CompactionBatchLimit ≤ 2^56` (a scope premise; etcd's default is 1000, `kvstore.go:44`).
  **Recommend (a).**
- **O4, the job's write-back tokens**: (a) the job draws from the server's receipt-funded pool
  (`srvWTPool`) through an mvcc-level pool contract (`□ (receipt ={⊤}=∗ WT)`); (b) `store.Compact`
  hands the job a bounded stock computed from the bucket's size (`⌈keys/limit⌉ + 1`); (c) make the
  write-back budget's bound a trust premise. **Recommend (a)** (no new premise; reuses D22 S7b's
  mechanism; check with the D22 owner since the pool is theirs).
- **O5, the `Cmp` parameter**: keep it with `kbCmp := True` (no churn in 17+16 files now) and remove
  it in a cleanup, or remove it in this stage. **Recommend keep, then clean up.**

**Estimate** (files whose statements or proofs change; counts by grep on `backend-cmp` at `7c03ace`):
backend model and invariants 8 files (`Model2`, `InvBackend`, `InvBatch`, `BatchLemmas`,
`CommitLemmas`, `WritebackLemmas`, `ReadSide`, `ReadLemmas`); backend specs/proofs 12-15
(`UnsafeDelete` ×2, `UnsafePut`/`SeqPut` ×4, `Unlock`, the RLocks ×2, `ConcurrentReadTx`, `Snapshot`,
`newBackend`/`New`/`NewAlloc`, `LockFor…` ×2); the bridge (2372 lines, 54 `bkLocked` uses) and
`StoreBackend`; mvcc: `InvStore` (`isKeyBackendG`, `batchTxSpecG`, `kbCmp`), `InvCompact`, the job
(729 lines), `store__compact`/`Compact`/`compactLockfree`; callers outside: about 20 files of
discharge changes (put premise 13, `UnsafeDelete` 4 in `etcdserver/`, `hookStep` 11, D22's clean
read 10, overlapping). Hardest: `cacheValid` through the commit path and `ConcurrentReadTx`, and the
bridge's soft `Unlock`. Next (Draft): write 3.1-3.5's statements with `sorry`, the bridge's glue
first (its 25 callee specs are the frame), then a review round before any backend proof.

## Scope decided (2026-10-28, the user's)

O1: the deletable keys a saved predicate fixed at the backend's creation (fallback, if the `▷` of
saved predicates' agreement blocks it: a pure key set mvcc vouches for in an invariant). O2: D22's
exactness through the `dlNone` token (an addition for D22, to be shown to its owner). O3: one-shot
delete permits from the limited range, with the scope premise `CompactionBatchLimit ≤ 2^56`. O4:
the job's write-back tokens from the server's receipt-funded pool (`srvWTPool`, D22's: check with
its owner before Draft). O5: `Cmp` kept, `kbCmp := True`, removed in a later cleanup. Next: Draft.

## Draft (2026-10-28, first round)

Written so far (statements; existing results unchanged except one marked step of the job):
- **mvcc's contract** (`mvcc/InvStore.lean`): `batchTxSpecG`/`isBatchTxG`/`isKeyBackendG` gain the
  one-shot delete permits `DP` (O3) and `isKeyBackendG` the safe-range slot `SR`/`SRh` (3.4), all
  defaulting to `True` (mvcc's assumed backend unchanged); the limited range's slices are lent
  against the session token (`rdCap`, and `rdCap2` for a key and its value read together: the job
  hashes both, which `rdCap` alone, the Scope draft's form, cannot lend) instead of read-only for
  good (3.5); `UnsafeDelete(Key)` spends a permit. The budgets `kbSR`, `kbWTSupply`,
  `compactJobRes` (3.4, O4) and the job's non-persistent precondition `compactJobPreR`
  (`mvcc/InvCompact.lean`; `compactJobPreR_none`: the assumed backend's instance).
- **The bridge** (`mvcc/BackendBridge.lean`): `isKeyBackendG_of_backendC`, `Cmp` true over the
  registered deletable keys `bkDel g`, the permits `bkDP gp` and the slot `srSlot`/`srHeld`; its
  non-compaction clauses are the old bridge's proofs, its four compaction clauses marked `sorry`
  (new cases). The old bridge stays, and `kbCmp` stays `kb = none`, until it is proved
  (a deviation from O5's timing: switching now would put the new cases' `sorry`s under every
  server result).
- **The backend** (`backend/DelKeys.lean`): `dlReg`/`dlIs` (O1), `thinV` (3.2), `dlNone` (O2),
  `safeStC` (3.1), `cacheValidC` (3.2), `viOk` (3.3); the specs' variants
  `batchTxBuffered.UnsafeDelete.specC` (any bucket, a safe-range key registered),
  `UnsafeSeqPut.specC` (above the committed keys too), `Unlock.specC` (the deleting session's
  branch, thin of the logical view).

**Found while drafting (for Review)**: (1) the job deletes `keys[i]`, a slice the range lends
against the session token, which `UnsafeDelete` also takes: the delete clause must accept a lent
slice (the job's proof has a marked `sorry` there); (2) `rdCap` lends one slice at a time, the
hasher reads two (hence `rdCap2`); (3) the registration's name `g` is explicit: `BNames` should hold
it, with `newBackend`'s creator fixing `Φ` (`NewAlloc`, its one construction site).

**Left for Draft's next round**: the backend invariants over the logical view (`γ.view` holding
`L`, `rtRest`/`batchGhostAt` thin, `cacheValid` → `cacheValidC`), `safeSt` → `safeStC` and
`BParams.VI` in place, `newBackend` returning `dlNone`, the slot and the registration, the
wiring (`storeBackend_of_backend` over the new bridge with `isKeyBackendG_congrDel`, `NewStore` and
`compactTok` carrying the budgets, `kbCmp := True`), and `metaVI`.

## Draft (2026-10-28, second round)

Done (`031e726c59`, `5c02b3d580`; full build passes):
- **The registration in `BNames`** (round 1's finding 3, O1): `BNames.dlg` (the deletable keys'
  saved predicate, allocated by the constructor at `False`) and `BNames.dln` (`dlNone`); the
  constructor's posts `newPost`/`newPostK` end with `dlInit γ` (the registration's whole fraction
  and `dlNone`, the creator's); `dlReg_fix` fixes the predicate once. `dlReg`/`dlIs`/`thinV`/
  `dlNone`/`cacheValidC`, the bridge's `bkDel` and the two spec variants are over the backend's
  names (no explicit `g`). D22's `SnapApplyWalk` and the server's `BootBackend` drop `dlInit` in
  their destructuring (mechanical: unused while the store keeps the old bridge).
- **`Unlock.specC`'s deleting branch** (finding 4): the writer's contents thin of the view the batch
  lock holds (`vData P (st.C, st.R)`), not of an existential view.
- **The delete clause takes the key lent** (finding 1): `isKeyBackendG`'s `UnsafeDelete(Key)` takes
  `rdCap Rd (Locked l) ∗ □ Rd key k`, as the limited range returns the key, instead of an owned
  slice; the job's delete step (`store.scheduleCompaction`) is glue, its sorry gone.

**Left** (measured this round):
- **`safeSt` in place** (3.1): dropping its third clause breaks the three lemmas establishing it
  (`BatchLemmas` 103, 133, 245: put, a non-safe-range delete, create; `DelKeys.safeStC_of`), and
  its one consumer is `BatchLemmas`' put lemma (116, 120), which carries the put condition from the
  writer's keys to the committed keys: there `UnsafeSeqPut`'s premise "above the committed keys"
  (`specC`) must take over, in place, with its callers (13 files) supplying it from mvcc's put
  condition. Tried and reverted (a re-proof, not a statement step).
- **The view's quarters over the logical view** (3.2): `batchGhostAt` (30 uses, 13 files), `rtRest`
  (26, 9), `cacheValid` → `cacheValidC` (18, 5): the quarters of `γ.view` hold the logical view
  with the physical one thin of it, which weakens every backend read spec from exact to thin
  (statements): the stage's core redesign, its own Draft round.
- **`BParams.VI`** (3.3): one use; with the `Meta` keys' clause.
- **The wiring** (`storeBackend_of_backend` over the new bridge, `isKeyBackendG_congrDel`, NewStore
  and `compactTok` with the budgets): after the above. **The `kbCmp := True` switch** needs: the new
  bridge's four `sorry`s proved (or the switch puts them under every server result), the server's
  `BootBackend` passing `dlInit` to mvcc (`dlReg_fix` at mvcc's `delKey`), and `newPost`'s
  `dlNone` routed to D22's exact-view users.

## After Review round 1 (2026-10-28, the user's)

Round 1 (`notes/spec-first-study/backend-review-1.md`): the design (a logical view, readers' views
missing only registered keys) is right; four of the new clauses are unprovable as stated (F1-F5),
`dlNone` is unsound as drafted (F6). Decisions:
- **F3: bbolt's `Bucket.Delete_kv` widened** to accept a key readable within its own transaction
  (true of bbolt v1.5.0: `bucket.go:518-532`, `node.go:145-159`, Delete copies what it needs). A
  trust-base change, recorded as such; to be covered by the Test step's bbolt tester (a Delete of a
  key returned by a range in the same transaction).
- **F6: `dlNone` dropped** (reverses O2): the unfixed registration (`dlInit`, before mvcc fixes the
  predicate) already rules out every deletable key, and D22's exact readers use that.
- **F10: the job's write-back tokens from a pool of its own** (revises O4), funded at `NewServer` from
  the time receipts: no share of D22's `E.γbe`, no coupling to D22.
Repairs without a decision: F1/F2 (the limited range lends against a per-call token and hands out the
delete capability over its own `Rd`), F4 (the delete permits a fixed stock per session), F5 (the
bridge's non-compaction clauses re-proved over the new `Locked`), F7 (`dlInit` kept unfixed for mvcc;
`isKeyBackendG_congrDel` under `▷`), F8 (`Unlock.specC`'s deleting branch also requires no puts to
non-hook buckets; the first branch dropped), F9 (`kbSR`/`srSlot` one definition), F11.

### Draft, round-1 repairs (2026-10-28)

- **F3** (`699bc59950`, the user's trust-base decision): bbolt's `Bucket.Delete_kv` takes the key
  owned or one of the transaction's own slices (`txBytes tx`), given back as taken (a flag `own`);
  `batchTx.UnsafeDelete`'s proof passes `own := true` (unchanged otherwise). `UnsafeDelete.specC`
  takes the same choice over the session's transaction. The trust base changes by this axiom's
  statement only (record it in `etc/tcb-baseline.txt`'s review when the stage merges).
- **F6**: `dlNone` and `BNames.dln` dropped; `dlInit` is the registration's whole fraction alone;
  `dlInit_noDel : dlInit γ ∗ dlIs γ nk ⊢ False` (an unfixed registration rules out every deletable
  key: `saved_pred_valid_2` with `DFrac.valid_own_op_discard`, no later), which D22's exact readers
  use.
- **F8**: `Unlock.specC`'s deleting branch requires no puts to the non-hook buckets and subsumes
  `viewSame`'s (one branch plus the clients'-view branch).
- **F9**: `backend.srSlot`/`srHeld` (`DelKeys.lean`), one definition; mvcc's `kbSR` over it.
- **F1/F2**: the limited range lends its slices against a token `T` of the call (`T ∗ (T -∗ Locked
  l)`, `rdCap Rd T`, `rdCap2 Rd T`) and returns the delete of a key it returned, over its own `Rd`
  and `T` (`{{ Key ↦□ b ∗ T ∗ Del k ∗ DP k ∗ □ Rd key k }} UnsafeDelete {{ T }}`); the separate
  lent-key delete clause is gone (the contract has nine clauses). The job threads `T` through its
  loop and takes the lock back after it (`store__scheduleCompaction.lean`, still proved). The
  bridge's two new cases (the delete, the range) are one `sorry` now.
- **F7** (recorded, not done): `SnapApplyWalk` keeps discarding `dlInit` until D22's exact readers
  are routed to it (a change to D22's statements, the wiring step's); `isKeyBackendG_congrDel` is
  to be stated under `▷` (`saved_pred_agree`) when it is written (the wiring step).
- **F5** (recorded): the new bridge's `Locked` must change (the deletes' `ndel`), so every clause
  over it is re-proved, not only the four new cases; the estimate in "Draft (second round)" grows
  by `bkLocked`'s 54 uses.
