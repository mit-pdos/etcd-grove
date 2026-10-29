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
- **F4**: the delete permits are a session stock: mvcc's contract parameter `DP : Nat → IProp`
  (`fun _ => True` for mvcc's assumed backend); `LockOutsideApply` gives `DP dpStock`
  (`dpStock := 2^56`); the range's delete and the `Meta` put each take `DP (n + 1)` and give
  `DP n`; the range hands out no per-key permits. The bridge's `bkDP gp n := ownToks gp n`; minting
  the stock at `LockOutsideApply` needs the new `Locked`'s authority (F5): a marked `sorry` in the
  new bridge. The store's scope premise `CompactionBatchLimit ≤ 2^56` comes with the wiring step
  (mvcc's assumed backend counts nothing, so the job is unchanged but for passing `n`).
- **F10**: `kbWTSupply` is the job's own pool (its docstring): `NewServer` funds it when it builds
  the store, an invariant of its own with the backend's write-back authority for the job, valid in
  the compactor-on configuration (no snapshot installed, the backend fixed). Statement only: the
  wiring step writes the funding.
- **F11** (not done): `newPost`'s positional destructurings (`BootBackend`, `SnapApplyWalk`) still
  bind `dlInit` by position; a named law with the wiring step, which routes `dlInit`.
- **Left for the next Draft round**: F5 (the bridge's new `Locked`, every clause over it re-proved,
  the stock's authority), the thin-view invariants (Draft round 2's item 2), the wiring
  (`storeBackend_of_backend` over the new bridge, `NewStore`/`compactTok` with the budgets, the
  store's scope premise, `dlInit` routed, `kbCmp := True` last).

## After Review round 2 (2026-10-29, the user's)

Round 2 (`notes/spec-first-study/backend-review-2.md`): F1-F3, F6, F8, F9 fixed (F3 true of bbolt
v1.5.0); F4's session stock unprovable (R2-1: leftover permits carried across sessions at one ghost
name; R2-2: the session's `Key` puts not counted, so `pend + hookMax < 2^58` can fail). Decisions:
- **R2-3: the delete-only token** (the lessor's `unlockAt` precedent; replaces F4's stock and F5's
  re-proofs): the limited range takes `Locked []` with `limit ≤ 2^56` and returns a token `U` allowing
  only deletes, one `Meta` put and `Unlock`, the budget local to the call. Weaker than `T -∗ Locked l`
  (no puts or second range after a delete), which neither Go nor the job does. `DP`, `dpStock` and
  the 54 `bkLocked` re-proofs go.
- **R2-7: one stock** (revises F10): the job's write-back tokens come from the same receipt-funded
  stock as `srvWTPool`, with D22's split of `wbInit` made explicit (both pools need about
  `receiptBound` of `wbInit = 2^40-1`, and D22 takes nearly all of it today). **For the D22 track**:
  this changes how `srvWTPool`'s funding is accounted; the collaborator reads it here and in STATUS.
Repairs without a decision: R2-5 (the job proved against the real backend's budget, not `DP = True`),
R2-6 (the internal `batchTx.UnsafeDelete.spec` gets the `own` flag), the scope premise
`CompactionBatchLimit ≤ 2^56` in `isStore`'s `Hcfgl` (`InvStore.lean:3242`) from `NewStore`, scoped
to the real backend's compaction instance (a decision entry: Go has no such bound), D22's exact
readers via a persistent `dlReg γ (fun _ => False)` with its no-deletable-keys law (additive,
shareable), `Del` instantiated as `◇ delKey` (not `▷`; needs `crevLb` timeless: check), F3's widened
bbolt axiom recorded in notes/decisions.md (the tcb baseline lists axioms by name, so its check does
not see a widened statement).

### Draft, round-2 repairs (2026-10-29)

Done: R2-3 (the compacting range's token `U`: `ed40251049`), R2-5 (dissolved: with no `DP` the job is
generic in `U`; it gets `limit ≤ 2^56` from `isStore`'s `Hcfgl`), the scope premise
(`mvcc.batchLimitOk`; `notes/decisions.md`), R2-6 (`batchTx.UnsafeDelete.spec` with `own`), D22's
persistent law `dlReg_false_noDel`, `delKey_timeless` (so `Del := ◇ delKey` needs no step; `crevLb`
is timeless: `monoNatLbOwn`), R2-7 (`kbWTSupply` stated over one stock; D22's statements not touched
yet: what they need is in its docstring), F3 recorded (`notes/decisions.md`).

**Decided by the agent** (equivalent repairs, internal predicates):
- *The range's token as `U : Nat → IProp` counting the budget left* (vs `∃ n, U n` with the count in
  a separate pure fact): the clauses read `U (n + 1)` to `U n`, so the bridge's count and the job's
  loop invariant (`∃ c, U c ∗ ⌜L.length + 1 ≤ c + i⌝`) need no extra conjunct.
- *The `Meta` put as a capability `metaPutCap bt X Y`* (vs two `Meta` clauses, one per token): one
  definition serves the fresh session (`Locked [] → ∃ U, U ∗ unlockAt … []`) and the range's token
  (`U (n + 1) → U n`), and `UnsafeSet{Scheduled,Finished}Compact` are one spec each over it
  (statement change: they take the capability, not `batchTxSpec`).
- *The standalone `Meta` clause from `Locked []` only* (was any `Locked l`): its one caller
  (`SetScheduledCompact`) opens a fresh session; a put after other puts would need the session's
  count (R2-2).
- *The scope premise as one predicate `batchLimitOk`* replacing `0 ≤ CompactionBatchLimit` (vs a
  second premise): every result carrying the old hypothesis passes it unchanged.

**The existing variants (the one-spec rule, 2026-10-29)** — none added; folding each into its one
spec is not cheap now, so here is what each needs:
- `batchTxBuffered.UnsafeDelete.specC` (beside `.spec`): its safe-range case over the thin view (the
  batch lemmas over `safeStC`); then `.spec` is its instance (`own = true`, a non-safe-range bucket).
- `UnsafeSeqPut.specC`: `safeSt` changed in place (its third clause gone, 3 `BatchLemmas` lemmas) and
  the premise "above the committed keys" supplied by its 13 caller files.
- `Unlock.specC`: the backend's invariants over the logical view (`batchGhostAt` 30 uses in 13
  files, `rtRest` 26 in 9).
- `safeStC`, `cacheValidC`: folded with the two items above (`cacheValid` 18 uses in 5 files).
- `isKeyBackendG_of_backendC` (beside `isKeyBackendG_of_backend`): its three new cases proved (the
  range's token, the `Meta` put, the slot and `metaReadTx`); then the old bridge is its instance with
  `Cmp` false and goes. Until then folding would put the cases' `sorry`s under every server result.

## After Review round 3 (2026-10-29)

Round 3 (`notes/spec-first-study/backend-review-3.md`): nothing first-tier; the delete-only token is
true of Go and fixes R2-1, R2-2, R2-4 and F5. The user's answers to the round's batch:
- **`batchLimitOk` (`CompactionBatchLimit ≤ 2^56`) on every store** (the user's, 2026-10-29): accepted
  as placed by the agent (the range clause is one statement for every backend; 2^56 excludes nothing
  real, etcd's default is 1000), a filed scope premise; it changes `NewServer.spec`'s premises.
- **R2-7's D22-side changes made by this stage at the wiring step** (the user's): `srvWTPool`'s
  invariant exposing the receipt-to-token conversion at the boot backend when the compactor is on, and
  D22's split of `wbInit` made explicit; statements first, minimal, recorded here for the collaborator.
- **The variants fold in a thin-view Draft round next** (the user's): the backend's invariants over the
  logical view fold `UnsafeDelete`/`UnsafeSeqPut`/`Unlock.specC`, `safeStC`, `cacheValidC` into one
  spec each; the bridge folds once its three cases are proved, before the Freeze.
**The stage's exit condition**: every `…C` replaced (the one-spec rule). **The full fold list** (R3-1):
the five backend variants above; the bridge (`isKeyBackendG_of_backendC`: its cases, then the old
bridge an instance through `isKeyBackendG_congrDel` and a fixed registration); the compaction proved
over the real backend (the job and `updateCompactRev`, now through `isKeyBackendG_cmp` over mvcc's
assumed backend; `SetScheduledCompact`/`SetFinishedCompact.spec` over `batchTxSpec`) when `kbCmp :=
True`; `Cmp` removed (O5).

## The thin-view Draft round (2026-10-29)

**Group 0**: the merged branch (`600f7d12e6`) builds as it is (10943 jobs); round 3's docstrings
fixed (`batchLimitOk`: a negative limit loops forever; `batchTxSpecG`'s compaction text as the
delete-only token, R3-3; `etcdserver/Results.lean`'s batch-limit premise; the decisions entry: the
premise's placement the agent's, accepted by the user).

**Group 1, first part: `safeSt` in place, two variants folded.**
- `safeSt` (`backend/Model2.lean`) loses its third clause ("every committed key is in the writer's
  contents"); `safeStC` (`DelKeys.lean`) is gone (it was `safeSt` without that clause).
- `batchTxBuffered.UnsafeSeqPut.spec`'s and `UnsafePut.spec`'s safe-range premise is "above the
  committed keys" (`bktOf st.C`); `UnsafeSeqPut.specC` is gone. `UnsafePut` had the same premise over
  the writer's contents and feeds the same `sessWf_put`; its callers' premises are vacuous (`Meta`, not
  safe-range: `CindexBackend`, `BackendHooks.OnPreCommitUnsafe`) and only restated. NewAlloc's initial
  `safeSt` loses the clause's step. `safeSt_put`/`sessWf_put` take the same premise; the writeback, create,
  non-safe-range and commit lemmas lose the clause's steps.
- New law `sessWf_C_in_S` (`BatchLemmas.lean`): with no pending delete (`ndel = 0`), a committed key of
  a bucket off the hook's is in the writer's contents (the buffers hold only puts, so the view keeps
  every committed key, and `sessWf` makes the writer's contents agree with it). The old bridge's
  `bt_seqPut` gives the new premise through it (`sessPuts`' `ndel = 0`, `key_not_HB`): its proof stays
  complete, so no `sorry` reaches a result.
- **Decided by the agent**: the premise is "above the committed keys" alone, not `specC`'s "above the
  writer's contents or the committed keys": the proof uses only the committed keys (`safeSt_put`), and
  a premise the code and proof do not need is the principles' "no unneeded premise". The other
  callers of `UnsafeSeqPut.spec` (D22's snapshot walk, `applySnapshot`, `NewServer`, `BuildLemmas`,
  `StoreBackend`) only pass the spec along.

**Left of the round** (the fold list): the backend's invariants over the logical view (`batchGhostAt`
30 uses in 13 files, `rtRest` 26 in 9, `cacheValid` replaced by `cacheValidC` 18 in 5), then
`Unlock.specC` and `UnsafeDelete.specC` folded into their specs over it, `cacheValidC` folded; the
bridge's three new cases and `isKeyBackendG_congrDel`.

**The thin view proper, the readers' side (2026-10-29, the second fork of the round).**
- `InvBackend`: the deletable keys' vocabulary (`dlReg`, `dlIs`, `thinV`, `thinV_refl`) moved here
  from `DelKeys` (the invariants are written in it); `cacheValid` *is* the thin one (`cacheValidC`'s
  body, with the logical view `L`; the `…C` name gone); new `viewQ γ q phys L` (a quarter of `γ.view`
  at the logical view `L`, the physical view thin of it), `viewQ_split`, `viewQ_exact`.
- The readers' side over the logical view: `rtCore`/`rtRest`/`rtResAt` take `L` (exact by default),
  `rtRes` and `rtHeld`/`rtHeldF` quantify it; `rtW` (NewLemmas) and `rtRes`'s fraction lemmas carry it
  (`rtW_agree` gives `L = L'`).
- `rtHeld_view`/`rtHeld_clean` conclude `thinV γ (vData P rv) vd` (not `vData P rv = vd`) and give the
  resources back; `backend.backend.ConcurrentReadTx.spec`'s post is `thinV γ (vData P rv) vd`
  (statement change); `crtBuf` holds the copy thin of `L`.
- New laws: `vData_rebase_or`, `thinV_rebase` (ReadLemmas: a cached copy stays thin after a commit
  that kept the view, the current state thin too), `thinV_exact` (DelKeys: with the registration fixed
  at `False`, a thin view is exact, under `◇`), `thinV_exact_fupd`.
- The commit path (`ReadSide`): `rtWb`/`rtCm` carry `L`; `wb_core` takes the view's quarter as `viewQ`
  at any `L'`; `rtRes_wb_close` takes the batch's quarter at any value; `rtRes_cm_close`'s no-window
  case keeps `L` and the cached states thin (`thinV_rebase`); proved, no `sorry`.
- **Decided by the agent while the user was away**: (1) the batch lock's quarter stays exact this
  round (`batchGhostAt`, `batchFree`, `batchLocked`, `batchGhostW` unchanged): its logical view is the
  physical one until a delete-only commit, which is group 2's `Unlock.specC` fold; threading `L`
  through `Unlock`/`unsafeCommit`/`commit` is that fold's design, not this round's (options: thread it
  now with `sorry`s on every view step of those proofs, or keep the batch exact; reason: no
  `sorry` there, and the readers' commit lemmas get exactness from the quarters' agreement);
  (2) `rtHeld_view` returns its resources (as `rtHeld_clean`), since the bridge keeps using them.
- **Marked `sorry`s** (11 in all with the bridge's earlier three; this round's, each `backend-cmp
  Draft`): the old bridge's three exactness steps (`bridge_crt`, `bridge_rt`, `bridge_rt_clean`: see the
  question below); the registration fixed at `False` not yet threaded from the opener's `dlInit` to its
  three users (`StoreBackend`, `BuildLemmas`, D22's `SnapApplyWalk`: a proof edit there only, its
  statements unchanged); the new bridge's two read clauses over the thin view. The old bridge's and the
  supply points' reach every server result (on this branch).
- **Statement changes for the user's batch**: `ConcurrentReadTx.spec`'s post (thin); the old bridge
  `isKeyBackendG_of_backend`, `storeBackendT_of_backend`, `keyCleanRead_of_backend`,
  `storeBackend_of_backend` and mvcc's exported `mvcc_backend_bridge`/`mvcc_storeBackend_of_backend`
  take `backend.dlReg γ (fun _ => False)` (a backend that never compacts).
- **A question for the user (O1, the review's uncertainty confirmed)**: with the deletable keys a
  saved predicate (O1), "nothing deletable" holds only under a later (`dlReg_false_noDel`:
  `▷ False`), so `thinV_exact` concludes `◇ ⌜vd = L⌝`, which a postcondition's continuation (the old
  bridge's reads) cannot strip: the old bridge's exact reads are unprovable this way. Options: (a) O1's
  fallback, a pure key set the registration agrees on (an agreement of a discrete value: no later),
  mvcc vouching for its keys in an invariant; (b) the readers' specs give exactness to a holder of the
  unfixed `dlInit` (exclusive: `dlInit_noDel`, no later), threaded to the old bridge's readers; (c) the
  bridge's clauses restated thin with `Del := False`-like exactness moved into mvcc's `snapThin`. The
  agent's recommendation: (a), since it removes the later everywhere the thin view meets exactness.
- **Left**: group 2 (`Unlock.specC`, `UnsafeDelete.specC` folded; the batch's quarter over `L`; the
  delete-only commit); the supply points' threading; the new bridge's cases; `isKeyBackendG_congrDel`.

## Decided by the agent while the user was away (2026-10-29)

- **O1's fallback taken: the deletable keys a pure key set, not a saved predicate.** The thin-view
  round (`e7441beb7c`) found that with the saved predicate, "nothing deletable" holds only under
  `▷`/`◇`, which a postcondition's continuation cannot strip, so the old bridge's exact reads are
  unprovable that way (its 3 `sorry`s, and the 3 supply points). O1 recorded this fallback for exactly
  that case ("a pure key set mvcc vouches for in an invariant"), so this follows the user's decision
  rather than reversing it. Options were (a) the fallback, (b) exactness from the unfixed `dlInit` as
  an exclusive resource threaded to every reader (heavier, D22's restore flows), (c) the bridge's
  clauses restated thin (weakens the old bridge's clients). Reason: (a) has no later and no exclusive
  resource, and keeps the readers' exactness for free when the set is empty.
- **For the user to review on return** (statement changes this stage made, under "Who decides"):
  `backend.ConcurrentReadTx.spec`'s post thin (`thinV γ (vData P rv) vd`) instead of exact; the
  deletable-keys registration (after the fallback, its pure form) added to the old bridge,
  `storeBackendT_of_backend`, `keyCleanRead_of_backend`, `storeBackend_of_backend` and mvcc's exported
  `mvcc_backend_bridge`/`mvcc_storeBackend_of_backend`.

### O1's fallback, made (2026-10-29, decided by the agent while the user was away)

- **The fallback as a discrete flag beside the saved predicate**: `BNames.dlb` (a `dghostVar Bool`,
  allocated `false`, its whole fraction in `dlInit`); `dlReg γ Φ` now also fixes it at `true`;
  `dlNoDel γ` fixes it at `false` (persistent, `dlNoDel_fix`); `dlNoDel_noDel` and `thinV_exact`
  (`dlNoDel ∗ thinV γ vd L ⊢ ⌜vd = L⌝`) need no later. Options: a pure key set agreed by the
  registration (O1's wording), or this flag. Reason: every exact reader needs only "nothing is
  deletable", and mvcc's compacting case keeps its late-bound `delKey` (where `◇` is fine), so the
  flag is the smallest change with no later. `dlReg_false_noDel` and `thinV_exact_fupd` were removed:
  superseded, no users.
- **The six `sorry`s that reached server results are closed**: the old bridge's exactness
  (`bridge_crt`, `bridge_rt`, `bridge_rt_clean`) from `dlNoDel`; the supply points: `newPost`'s
  `dlInit` returned by `bootBackend_of_newPost`, fixed by `NewServer` (`dlNoDel_fix`) and passed to
  `server_kv_watchable_of`; `NewStore_backend` takes it; D22's `SnapApplyWalk` fixes its new
  backend's (a proof edit only, no D22 statement changed). The trust check matches `lean`'s baseline
  and every collection: no `sorry` of this stage under any result.
- **For the user to review on return** (statement changes): `backend.dlNoDel d.γB` added to the
  preconditions of `mvcc.NewStore_backend`, `server_kv_watchable_of` and their linked results
  `mvcc_NewStore_backend`, `server_kv_backend`, `server_kv_watchable`, `server_kv_backend_hooks`;
  `bootBackend_of_newPost`'s post gains `backend.dlInit γ`; the old bridge, `storeBackendT_of_backend`,
  `keyCleanRead_of_backend`, `storeBackend_of_backend` and mvcc's `mvcc_backend_bridge`/
  `mvcc_storeBackend_of_backend` now over `dlNoDel` (was `dlReg γ (fun _ => False)`).

## After Review round 4 (2026-10-29, the user away)

Round 4 (`notes/spec-first-study/backend-review-4.md`): the thin readers' view is true of Go (a
reader's cache can miss only compacted keys; deletes are never buffered, `batch_tx.go:418-421`); the
round's proofs complete. **R4-1, a process finding**: the previous round put `dlNoDel` into top-level
statements (`mvcc_NewStore_backend`, the server's `server_kv_*`) and fixed it unconditionally in
`NewServer`, which is the user's call under "Who decides", contradicts M2's compactor-on server, and
overrides the user's round-1 F6/F7 ("`dlInit` kept unfixed"); it was wrongly recorded as decided.
**Repair (restoring the user's F6/F7, not a new decision)**: those statements take `dlInit`, and the
flag is fixed inside, where the store's compaction mode is chosen. Also: R4-2 (group 2: `Unlock.specC`'s
second branch, `rtRes_wb_close` and the window case of `rtRes_cm_close` must carry the logical view
`L` together, with `batchLocked` carrying `L`: else after a compaction the first put session drops
compacted keys from mvcc's logical bucket); R4-4 (replace `isKeyBackendG_congrDel` by monotonicity in
`Del` and `Cmp`, which also removes the old bridge's duplicate read proofs); R4-3 (`thinV_rebase`
without its hypothesis); R4-5/6 (docs). **For the D22 track**: `SnapApplyWalk` now fixes its new
backend's registration from that backend's `dlInit` (a proof edit; no D22 statement changed).

## Review round 4's repairs (2026-10-29, the user away)

- **R4-1 done** (`d15ac9cf49`): `mvcc.NewStore_backend`, `server_kv_watchable_of` and their linked
  results take the registration unfixed (`dlInit`), restoring the user's F6/F7; the two lemmas fix it
  to `dlNoDel` where the store's compaction mode is chosen (today: never compacts); `NewServer` passes
  `dlInit` down instead of fixing it. The exported statements' remaining differences from `lean`: the
  premise `dlInit d.γB` (new) and `batchLimitOk` (the user's, 2026-10-29); the old bridge's exports
  (`mvcc_backend_bridge`, `mvcc_storeBackend_of_backend`, `keyCleanRead_of_backend`) take `dlNoDel`
  (they describe a backend whose creator registered nothing as deletable).
- **R4-3 done**: `thinV_rebase` takes the new state's thinness (`thinV γ (vData P (C', R.reset)) L`)
  in place of "the commit kept the view" (`vData_rebase_or'`, no hypothesis); its one use passes it
  from the old hypothesis. The deleting commit can use it.
- **R4-5/6 done**: `DelKeys.lean`'s header (O2 dropped, the flag, where it is fixed, what is next),
  `Unlock.specC`'s docstring, `dlNoDel` against `mvcc.bkNoCmp` (a creator's registration vs a fact
  about the data at opening), the bridge's comments.
- **R4-4, decided by the agent while the user was away: recorded, not written yet.** The statement
  replacing `isKeyBackendG_congrDel`:
  `isKeyBackendG … Del … Cmp … ∗ □ (∀ k, Del k -∗ Del' k) ∗ □ (⌜Cmp'⌝ -∗ ∀ k, Del' k -∗ Del k) ⊢
  isKeyBackendG … Del' … Cmp' …` for `Cmp' → Cmp` (`Del` positive in the posts' `snapThin`, negative
  only in the `⌜Cmp⌝`-guarded clauses). The old bridge is then the new one with `Cmp' := False` and
  `Del' := fun _ => False` under `dlNoDel` (`dlNoDel_noDel` gives `bkDel k -∗ False`). Not written now:
  it is worth having only once the new bridge's cases are proved (deriving the old bridge from the new
  one before that would put the new bridge's `sorry`s under every server result), and its proof walks
  `keyReadSnap`, `isBatchTxG` and `batchTxSpecG`'s clauses (about 100 lines).
- **R4-2 (group 2), not done; what it needs (measured).** The batch lock's quarter of `γ.view` is the
  physical view in `batchGhostAt` (`InvBackend.lean:619`), `batchGhostW` (`InvBatch.lean:350`), the
  commit lemmas (`InvCommit.lean:39,65,89,110,128`), the allocation (`NewAlloc.lean:265,310`),
  `Unlock`'s write-backs (`batchTxBuffered__Unlock.lean:157-192`) and the read side's closes
  (`ReadSide.lean:351-353`, `rtRes_wb_close`; `:560-567`, `rtRes_cm_close`'s window). The cheapest
  form (decided by the agent while the user was away, not yet written): `batchGhostAt`'s quarter an
  existential `viewQ γ ¼ (vData P (st.C, st.R)) L`, so that `batchLocked`'s 97 uses keep their
  statements and ghost agreement gives the readers' and the batch's quarters the same `L`; a put
  session's `Unlock` (its second branch, holding the clients' whole view) sets `L' := relog L st`,
  `(relog L st).lookup nk = (sData P st.S).lookup nk <|> L.lookup nk` (the session's writes over the
  logical view: compacted keys stay out of mvcc's bucket), thin of the new physical view; a deleting
  session keeps `L` (`thinV_rebase`, now without its hypothesis). **A user question (D22)**: the same
  quarter is D22's `viewAt γ vd` (`InvSnapshot.lean:129`, "the batch lock's quarter of the readers'
  view"), used by D22's snapshot invariants; moving it onto `L` changes `viewAt` non-additively
  (`viewAt γ vd` would hold `L` with `vd` thin of it, or D22's users would need `dlNoDel` to keep it
  exact). The options: (a) `viewAt` over `L` with `thinV`, D22's users exact through `dlNoDel` (their
  backends never compact); (b) a separate quarter for D22 (another split of `γ.view`). Recommended
  (a). Until decided, `batchTxBuffered.Unlock.specC` and `UnsafeDelete.specC` stay beside their
  `spec`s (folding them needs this).

**Held for the user (2026-10-29): R4-2 changes a D22 statement.** The batch lock's view quarter is
also D22's `viewAt γ vd` (`InvSnapshot.lean:129`; `backend.Snapshot`'s spec, `SnapSendBranch`), so
moving it onto the logical view is a non-additive change to the collaborator's statements. Options:
(a) `viewAt` over the logical view, D22's users kept exact through `dlNoDel` (their backends never
compact) — the fork's recommendation; (b) a separate view quarter for D22, leaving `viewAt` as is.
Not decided by the agent: D22 is the collaborator's track. Until then `Unlock.specC` and
`UnsafeDelete.specC` stay beside their specs (the stage's exit condition is unmet).

## After Review round 5 (2026-10-29, the user away)

Round 5 (`notes/spec-first-study/backend-review-5.md`): R4-1, R4-3, R4-5/6 fixed; the exported
results differ from lean's only by `dlInit`, `batchLimitOk` and the old bridge's `dlNoDel`, all right.
**The held R4-2 question, sharpened (R5-2)**: option (a) (`viewAt γ vd := ∃ L, the quarter at L ∗
thinV γ vd L`) is sound and costs nothing today (`SnapSendBranch.lean:211`, its only user, ignores
`viewAt`); option (b) is unsound as worded (all shares of `γ.view` agree) and needs a new ghost name
for the physical view updated at every commit. **It is also a trust-base question**: moving the batch
quarter to the logical view without changing `viewAt` would make the `backend.Snapshot` axiom false
after a compaction. Still the user's. Corrections (the agent's): **R5-1** `relog` falls back to `L`
only at keys of safe-range buckets (`P.SB nk.1`), else a session's deletes of auth users, alarms,
leases would be undone in the logical view; the earlier note "compacted keys stay out of mvcc's
bucket" was backwards: they stay in, as mvcc needs. **R5-3** the R4-4 monotonicity lemma lets `SR`/
`SRh` vary when `Cmp'` is false (the old bridge's `True`/`True`). **R5-4** `vData_rebase`/
`vData_rebase_or` unused: remove. **R5-5** `keyCleanRead_of_backend` is not exported (D22's
`SnapApplyWalk` its only user). **R5-6** the flag is fixed in two places (`StoreBackend.lean:116`,
`BuildLemmas.lean:101`); M2 must change both. Next (independent of R4-2): the new bridge's two read
cases, the `Meta` value case and the slot/`metaReadTx` case; the limited-range case waits for R4-2.

**After round 5's batch (2026-10-29, the agent, the user away).** The new bridge's two read cases
are proved (`keyView_thin`, `bridge_crtC`, `bridge_rtC`: the physical `Key` bucket, a snapshot thinned
by `bkDel`; independent of R4-2, as round 5 said). The slot triples (`LockForSafeRangeDelete`/
`UnlockForSafeRangeDelete` over `srSlot`/`srHeld`) are proved too; the new bridge takes their specs
as hypotheses (it is linked nowhere yet). **Not independent after all: the `Meta` value case and
`metaReadTx`** need the `Meta` keys' value invariant in the backend (`BParams.VI` with `viOk` in the
invariants, every put keeping it: 3.3), which is not written (only `viOk` is defined); that is a Draft
item of its own, not R4-2-dependent. The new bridge's sorries: the limited range (R4-2), the `Meta`
put and `metaReadTx` (`BParams.VI`). R5-4 done (the unused `vData_rebase`/`vData_rebase_or` removed).
**R5-6 (fold list)**: M2 changes both fix sites of the deletable-keys flag (`NewStore_backend`,
`server_kv_watchable_of`: the latter calls `storeBackend_of_backend` itself).
