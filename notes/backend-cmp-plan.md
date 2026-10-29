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

## The `Meta` cases (2026-10-29, the user away)

- **The new bridge's `Meta` put case proved** (`bt_metaPut`, `BackendBridge.lean`): the backend's
  `UnsafePut` into the hook bucket `Meta` from the lock with no puts, to the token `bkLockedO … 1`
  (one operation over the free lock, nothing the readers see changed: `viewSame_putHB`, with
  `sData_insert_HB`), which only `Unlock` takes (`bt_unlockOAt`). It needs no value invariant: the
  value's form matters to a reader of `Meta`, not to the put. The new bridge gains two hypotheses
  (it is linked nowhere): `UnsafePut.spec`, and `hHK` (a compaction key is not a hook's own key,
  true of `KBReal.P`: its `HK` is the consistent index's two keys).
- **`metaPutCap` repaired** (decided by the agent while the user was away; a finding for review round
  6): it lent the key and value slices fractionally (`↦*{dq}`) and gave them back, which no buffering
  backend can meet (the write buffer keeps the slices: `txWriteBuffer.put`); it now takes them
  read-only for good (`↦*□`) and gives nothing back. Its two callers, `UnsafeSet{Scheduled,Finished}
  Compact`, persist their fresh `rbytes` (never written again, as in Go). Options were this or a copy
  in the contract's statement (no such copy in Go).
- **`metaReadTx` needs more than the value invariant** (a finding for review round 6; not done): the
  contract's `ReadTx` clause gives `metaReadTx rt` with `RLock`/`RUnlock`/`UnsafeRange` at
  precondition `True`, while the real backend's `readTx.RLock` needs a reader token and an open share
  (`rdTok`, `bOpen`) and its `UnsafeRange` the held lock (`rtHeldF`), lending its slices against it
  (`kvsOutRd`): "a contract with no resource over a callee that needs one". The repair is a restated
  `metaReadTx` threading the read token (as `keyReadLocked`/`rdCap` do) — mvcc's contract, used by
  `checkPrevCompactionCompleted` (proved over mvcc's assumed backend) — and then `BParams.VI` for
  `metaRevVal` (3.3). The cindex's `metaReadTx` (`etcdserver/InvCindex.lean:207`, the consistent
  index's keys, proved over the real backend through the hook's keys) is the precedent to follow.
  The value invariant was not started: alone it closes nothing.

## `metaReadTx` and `BParams.VI`: blocked on the trust base (2026-10-29, the user away)

**Finding.** Restating mvcc's `metaReadTx` so the real backend can meet it (thread the backend's read
token `RT` into `RLock`, give it back at `RUnlock`, lend the read slices against the held lock via
`rdCap`, as the real backend's `readTx.RLock`/`UnsafeRange`/`RUnlock` specs require: `rdTok ∗ bOpen`,
`rtHeld`, `kvsOutRd`) means restating `metaReadSpec` (`InvStore.lean:599`). That definition is also
the statement of the **axiom `mvcc.kbNoCmp_metaNone`** (`NoCmpRead.lean`, the restore plan's R4c,
D22's restore path), which gives `□ metaReadSpec rt true` with no token. So the restatement changes
an axiom's statement (the trust base: the user's), and a token-threaded twin beside `metaReadSpec`
would be a second spec family (the one-spec rule: the user's). Not done; no code changed.
`checkPrevCompactionCompleted` itself would be fine: it is proved over mvcc's assumed backend
(`storeCmp`, `kb = none`), where `kbRT none = True`.

**Question for the user** (options):
(a) generalize `metaReadSpec` with a lock token `Tok` and lent slices (`rdCap Rd Tok`), and restate the
axiom `kbNoCmp_metaNone` over it (`Tok` and `Rd` from the `keyReadSnap`/`keyReadSnapC` it already
takes) — the axiom stays a statement about a backend recording no compaction; the restore's proof and
`UnsafeRead{Scheduled,Finished}Compact` (98/99 lines) adapt to read under the token. Recommended.
(b) keep `metaReadSpec` and the axiom; give the compaction's `Cmp` clause its own token-threaded
reads with a new name — a second family beside `metaReadSpec` (against the one-spec rule).
Where the real backend's `RT` comes from at the compaction (the apply thread's `writerOwn` holds a
`storeRT`; `store.Compact.spec` would take it) is a wiring-step question, also the user's (it changes
`store.Compact.spec`, what mvcc's client sees).

**`BParams.VI`, designed, not written** (it is useful only once (a) or (b) is decided): `VI n k v :=
n = Meta ∧ metaCompactKey k → metaRevVal v` (true for every other bucket and for the hook's own keys,
which are not compaction keys: the bridge's `hHK`); a clause of `safeSt` (committed contents and the
buffers satisfy `viOk P.VI`), kept by `UnsafePut`/`UnsafeSeqPut` under a new premise `P.VI n k v`
(trivial for `VI := fun _ _ _ => True`, the default for every `BParams` but the bridge's), and a law
that a reader's view (`rtHeld … rv`) satisfies it (from `vData`'s two parts). Cost: `BParams`' field
(every construction), `safeSt`'s establishing lemmas (`BatchLemmas`), the put specs' 13+ callers, the
readers' law through `rtCore`.

## Paused for the user's answers (2026-10-29): the batch

Review round 6 (`notes/spec-first-study/backend-review-6.md`) confirms the round's proofs (the bridge's
read, slot and `Meta`-put cases; `metaPutCap`'s read-only-for-good slices, true of Go and within the
agent's remit). Every remaining `sorry` of the stage now waits on the user; the stage is paused here.
This section supersedes the earlier statements of the questions (R6-6).

1. **An axiom on `lean` false as stated (R6-1).** `mvcc.kbNoCmp_metaNone` (`NoCmpRead.lean:38`, the
   restore work's R5c, `etc/tcb-baseline.txt:570`) leaves `rt`, `RT`, `Del`, `m`, `L` free: from one
   backend's `kbNoCmp` it concludes `metaReadSpec rt true` for any read transaction (with `L := False`
   the antecedent holds of any `rt`), so a second backend's read over a file holding
   `finishedCompactRev` is claimed to find nothing, which Go contradicts (`read_tx.go:78-89`); and it
   is applied before `RLock`, so it outlives the read. Probably no `False` in Lean (no backend spec pins
   a `Meta` read), but false of the code. Proposed fix (a′, the reviewer's): the fact stated at the
   backend, tied to its `readTx` through `rtHeld`, consumed by one read and true of that read only.
   The trust base and the restore (D22) track: the user's. **Confirmed by the `axiom` skill
   (2026-10-29, branch `axiom/kbnocmp-metanone`, `notes/axiom-review/nocmpread.md`):** a Go program
   that panics on the backend's own `ReadTx` after `Compact` is proved to return from the axiom, no
   `sorry`.
2. **R4-2: D22's `viewAt` with the batch quarter on the logical view.** (a) `viewAt γ vd := ∃ L, the
   quarter at L ∗ thinV γ vd L`: sound, costs nothing today (its only user ignores it) — recommended;
   (b) a separate physical-view ghost name updated at every commit: sound only so, heavier. Also a
   trust-base point: without changing `viewAt`, the `backend.Snapshot` axiom becomes false after a
   compaction. Blocks: the limited-range `sorry`, folding `Unlock.specC`/`UnsafeDelete.specC`.
3. **`metaReadSpec` (the statement of question 1's axiom).** Restate it with the lock token and lent
   slices (with question 1's fix), or a separate clause (breaks the one-spec rule). Blocks the
   `metaReadTx` `sorry`. Note (R6-2): the cindex's `metaReadTx` is an unproved premise of the same
   token-free shape (`CindexBackend.lean:27-30`), not a proved precedent.
4. **`BParams.VI` and the trust base (R6-3).** Putting `viOk` into `safeSt` would make the `OpenBackend`
   axiom claim it of any file on disk unless `openPre` gains a premise: the user's.
5. **The compaction's read token at wiring.** Cheapest: `store.Compact.spec` lends `storeRT` from the
   apply thread's `writerOwn` (as `restore` takes a token from its caller): a statement mvcc's client
   sees, so the user's.
Statement changes made while the user was away, for review (see the sections above): `ConcurrentReadTx`
's post thin; `dlInit` a premise of the exported `mvcc_NewStore_backend` and `server_kv_*` results;
the old bridge's exports over `dlNoDel`; `metaPutCap`'s slices read-only for good.

## The compaction keys' tracked absence (the user's choice, 2026-10-29)

**Why.** The `axiom` skill refuted `mvcc.kbNoCmp_metaNone` (branch `axiom/kbnocmp-metanone`,
`notes/axiom-review/nocmpread.md`). The restatement first proposed for it (anchor the reader,
hold the fact under its lock) is false too: the backend's proved `UnsafePut` lets any holder of
the batch lock write a compaction key into `Meta`, and a later read finds it. The user chose the
design below (question 1 of the batch), together with question 3 (`metaReadSpec` with the lock
token and lent slices).

**Design (Scope; statements to Draft).**
- **The parameter.** `BParams.FK : GoString → GoString → Bool` names the tracked-absent keys.
  - `KBReal.P` sets `FK n k := n = Meta ∧ metaCompactKey k`; every other `BParams` sets
    `fun _ _ => false`.
  - `BParams.Wf` gains: an `FK` key is not a hook's own key (`P.hk`), and not in a safe-range
    bucket.
- **The ghost.** `γ.fk` is a `monoNat`. `0` means no `FK` key anywhere; `1` means some may be.
  - The batch lock's ghost (`batchGhostAt`) holds half of its authority, with
    `n = 0 → fkAbsSt P st`: no `FK` key in the committed data, the writer's contents, the read
    buffer's view, or the write buffer's.
  - The client holds the other half: `fkOwn γ n`.
  - The readers' state (`rtCore`) holds a lower bound `n0` taken when its `rv` was set, with
    `n0 = 0 → fkAbsRv P rv`. It is updated where `safeRv P rv` is.
- **The put specs.** The `UnsafePut`/`UnsafeSeqPut` specs of `batchTxBuffered` and `batchTx` take
  `fkPut γ P n k`: `∃ v, fkOwn γ v` if `P.FK n k`, else `True`. Their posts give `fkOwn γ 1` in the
  first case.
- **The read law.** `fkOwn γ 0 ∗ rtHeldF γ P b rtx rv p ⊢ ⌜fkAbsRv P rv⌝`, so `rtRange` at an `FK`
  key is empty.
- **Creation.**
  - `New`/`newBackend` give the creator `fkOwn γ (if fkAbsD P D then 0 else 1)`.
  - `storage.OpenBackend`'s axiom gives `⌜noCmpData D⌝ -∗ bkNoCmp γ` as today, but `bkNoCmp`
    is no longer opaque: it is defined as `fkOwn γB 0` (for `KBReal.P`, `fkAbsD ↔ noCmpData`).
    The statement's text is the same and its meaning is new: a trusted-statement change, the
    user's choice.
- **mvcc's contract.**
  - `metaReadSpec rt nc Rd Tok` reads under the reader's token `Tok`, with the value's slices
    readable through `Rd` (question 3).
  - `keyReadLocked`'s `rng = true` branch, the `ReadTx` reader, gains
    `□ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok)`. `NC` is a new parameter of
    `keyReadLocked`/`keyReadSnap`/`keyReadSnapC`/`isKeyBackendG`/`keyCleanRead`, defaulting
    to `False`.
  - The store passes `NC := kbNoCmp γ.kb γ.bucket`. The bridges prove the clause from the read law.
- **The axiom.** `mvcc.kbNoCmp_metaNone` is deleted. `store.restore` takes the meta reads from its
  reader's clause, with its spec unchanged (it still consumes `kbNoCmp`).
- **Left for the wiring step.** The real store's compaction must put the compaction keys
  (`metaPutCap`, the new bridge's `bt_metaPut`), which now needs `fkOwn`. `restore` would then hand
  the token to the store instead of consuming it: a change to `store.restore`'s spec, the user's
  (with question 5).

### Done (2026-10-29): the tracked absence, with review round 7's repairs

Review round 7 (`notes/spec-first-study/backend-review-7.md`) ran on the Scope above; its findings
are applied as follows. Everything builds (`lake build`); `etc/tcb-report.py --check` differs only by
the removal of `mvcc.kbNoCmp_metaNone` (baseline and the ten collections that listed it updated).

**Backend.**
- `fkKey` (`Model2.lean`) fixes the tracked keys: `Meta`'s `scheduledCompactRev` and
  `finishedCompactRev`. *Decided by the agent:* no `BParams.FK` field. The backend serves one schema,
  and a fixed set makes `fkAbsD D ↔ noCmpData D` for every `P`. That removes R7-1's arbitrary-`P` half,
  and with it the `Wf` clauses (R7-5's safe-range question is moot).
- The ghost `γ.fk` (`monoNat`):
  - the batch lock's half, `fkHalf` (in `batchGhostAt`/`batchGhostW`);
  - the client's half, `fkOwn`;
  - the readers' lower bound, `fkRd` (last conjunct of `rtCore`). It is set where `rv` changes:
    the constructor, the `Unlock`'s write-back (`wb_core`) and the commit (`rtRes_cm_close`).
- Each state transition keeps `fkAbsSt` (`FkLemmas.lean`). The put case raises the flag
  (`fkHalf_put`, `fkHalf_raise`).
- `batchTxBuffered.UnsafePut.spec` takes and returns `fkPut γ bi.name kb` (R7-4).
  `UnsafeSeqPut.spec` takes the pure premise `¬ fkKey bi.name kb`. The inner `batchTx` specs are
  unchanged.
- The read law, as R7-2 asks: `rtHeldF_fkRd`/`rtHeld_fkRd` (the persistent witness) and `fkRd_abs`
  (with `fkOwn γ 0`).
- `newPost`/`newPostK` carry `fkOwn γ (fkInit D)`. `New`/`newBackend`'s spec text is unchanged; the
  definition changed.

**Trusted statements** (R7-1, R7-3):
- `storage.OpenBackend.spec` (T): the wand `(⌜noCmpData D⌝ -∗ bkNoCmp γ)` is dropped. The post is
  `newPostK γ P W Pk K b D`, which holds the half.
- `storage.OpenSnapshotBackend.spec` (E): the same wand is dropped.
- `bootOk` (premise of `NewServer.spec`). **The user's decision, 2026-10-29:** `"Hncmp" ∷ mvcc.bkNoCmp
  d.γB` becomes `"%HnoCmp" ∷ ⌜mvcc.noCmpData D⌝`. `bootBackend_of_newPost` derives `bkNoCmp` from
  `newPost`'s half (`mvcc.bkNoCmp_of_fkOwn`).
- `mvcc.bkNoCmp γB := backend.fkOwn γB 0`. It is a definition now, no longer opaque. The exported
  results' premise `bkNoCmp d.γB` keeps its text and changes meaning. None of them also takes
  `newPost`.

**mvcc.**
- `metaReadSpec rt nc Rd Tok` reads under the token, its value slices through `Rd` (question 3).
  It is persistent (`metaReadSpec_persistent`).
- `metaReadTx rt`: `RLock` gives `Tok`, `rdCap`, the reads, and `RUnlock` from `Tok`.
- `NC` is explicit at every use, with no default (R7-6), on:
  - `keyReadLocked RT NC …`;
  - `keyReadSnap View RT NC Del …`;
  - `keyReadSnapC View RT NC …`;
  - `isKeyBackendG b View RT WT NC …`;
  - `keyCleanRead b View RT NC`.

  The clause `□ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok)` is in `keyReadLocked`'s `rng` branch
  (`keyReadLocked_meta`). `keyReadLocked_weaken` drops to `rng = false` at any `NC'`.
- The store passes `kbNoCmp γ.kb γ.bucket` (in `storeBackend`, `storeBackendT`, `physOk`, `txReader`,
  `restoreView`). That gives these statement changes:
  - `store.restore.spec`: `isKeyBackendG … (kbNoCmp γ.kb γ.bucket) …`;
  - `store.Restore.spec`, `watchableStore.Restore.spec`: `keyCleanRead … (kbNoCmp …)`;
  - `rangeEvents.spec`: quantifies `NC`;
  - `UnsafeRead{Finished,Scheduled}Compact.spec`: `□ metaReadSpec rt nc Rd Tok ∗ rdCap Rd Tok ∗ Tok`,
    with `Tok` returned.
- The bridges prove the clause through `rt_metaNone`:
  - `rt_locked` takes `fkRd γ P rv`;
  - `bridge_rt`, `bridge_rt_clean` and `bridge_rtC` take it from `rtHeld_fkRd`;
  - their `NC` is `bkNoCmp γ`;
  - `crt_locked` is at any `NC` (`rng = false`).
- `store.restore` takes its two reads from `keyReadLocked_meta`, consuming `kbNoCmp`. The axiom
  `mvcc.kbNoCmp_metaNone` and `NoCmpRead.lean` are deleted.
- `metaReadTx`'s value case for the real backend stays blocked on `BParams.VI` (question 4): its
  `sorry` is unchanged.

**Decided by the agent while the user was away (for review):**
- **The right to write the compaction keys in the contract.** The new bridge's `Meta` put
  (`bt_metaPut`) now needs the client's half (`fkPut`). The contract's `Cmp` clause therefore reads
  `metaPutCap bt (Locked [] ∗ MW) ((∃ U, …) ∗ MW)`. `MW` is a new trailing parameter, defaulting to
  `True`, of `batchTxSpecG`/`isBatchTxG`/`isKeyBackendG` (as `SR`/`SRh` are).
  - The new bridge exports it at `MW := ∃ f, fkOwn γ f`.
  - No proved store uses that clause over the real backend. `SetScheduledCompact`/
    `SetFinishedCompact` (mvcc's assumed backend) pass `True`.
  - At wiring, the store must hold the half: `restore` hands it on instead of consuming
    `kbNoCmp` (question 5's companion; the user's).
- The other options were an `isKeyBackendG` parameter without a default (more churn, against
  `SR`/`SRh`'s precedent), or leaving `bt_metaPut` unproved (against "never delete a finished
  proof").

### Review round 8's repairs (2026-10-29)

Review round 8 (`notes/spec-first-study/backend-review-8.md`, committed with these repairs).
`lake build` passes; `etc/tcb-report.py --check` and `etc/gen-init.py --check` pass unchanged.

- **R8-1 (fixed).** The compacting range's step put of `finishedCompactRev` bypassed the flag:
  `batchTxSpecG`'s clause gave `□ ∀ n, metaPutCap bt (U (n + 1)) (U n)`. That made
  `isKeyBackendG_of_backendC` false as stated, its `sorry` case unprovable. It now reads
  `□ ∀ n, metaPutCap bt (U (n + 1) ∗ MW) (U n ∗ MW)`.
  - The job's caller (`store.scheduleCompaction`, over mvcc's assumed backend) frames
    `kbMW none = True`.
  - The case is again provable from `bt_metaPut`'s pattern, once the job holds the right. That is
    the wiring step, as for `SetScheduledCompact`.
  - Neither `Meta` clause (the fresh session's put, the job's step put) is used by a proved store over
    the real backend.
- **R8-2 (fixed, with one part decided by the agent).** `MW` no longer has a default. It is explicit
  on `batchTxSpecG`, `isBatchTxG` and `isKeyBackendG`. The store names it `kbMW γ.kb` (in
  `storeBackend`, `storeBackendT`, `physOk`, the `#Hbt` facts and `batchTxSpec`), and the specs
  `store.restore` and `rangeEvents` quantify it.
  - `kbMW (some d) := ∃ f, fkOwn d.γB f`.
  - *Decided by the agent while the user was away:* `kbMW none := True`, not the reviewer's opaque
    `viewFk` (with `viewNoCmp γb := viewFk γb 0` and `MW := ∃ f, viewFk γb f`). With `viewFk`, the
    store's proved compaction over mvcc's assumed backend (`SetScheduledCompact` in
    `updateCompactRev`, the job's `UnsafeSetFinishedCompact`) would need the store to hold the right.
    That is the wiring step's change to `store.restore`'s spec (hand the half to the store instead of
    consuming `kbNoCmp`): the user's decision, with question 5.
  - Until then the assumed instance pairs `NC = viewNoCmp` with `MW = True`, which no honest creator
    can meet. But `viewNoCmp` has no supplier in the repository, so results over `kb = none` that take
    `kbNoCmp` are vacuous, not wrong (`kbMW`'s docstring says so).
- **R8-3 (recorded).** `fkKey` fixed inside the backend: `notes/decisions.md`, "The compaction keys
  tracked inside the backend".
- **R8-4 (docs).**
  - `UnsafePut`'s and `fkPut`'s docstrings say the half comes back "at some value", without "raised".
  - `rtCore`'s docstring traces `CommitAndStop`: it goes through `commit` and `unsafeCommit`, and
    `rtRes_cm_close`'s stop branch sets `fkRd`.
  - Trust base: the axioms whose meaning moved through `isBackend`/`batchLocked` (which now carry
    `fkHalf`) stay true:
    - `backend.backend.Snapshot.wp_proof` only commits, and a commit keeps `fkAbsSt`
      (`fkAbsSt_commit`).
    - `schema.membershipBackend.MustSaveMemberToBackend` puts into `members` only, not a `fkKey`.
    - `MustUnsafePutLease` and `UnsafeDeleteLease` take the caller's own triple of the batch
      transaction, so the flag is the caller's business. Their puts and deletes are to the `lease`
      bucket, not `Meta`.
- **R8-5 (note, under question 4).** `BParams.VI` could ride on the same ghost. `fkHalf` is the one
  place every write of the compaction keys passes through. A conjunct "every `fkKey` value in `st`
  satisfies `metaRevVal`" would have these properties:
  - `fkHalf_put` would keep it, with `UnsafePut` taking `metaRevVal v` at an `fkKey`;
  - readers would get it through `fkRd`, as `fkAbsRv`;
  - its cost is a premise on the opened file's values at those keys.

  This would close `metaReadTx`'s value case without a new `BParams` field. Not done: it is
  question 4's answer.

### Review round 9 and the end of this increment (2026-10-29)

Round 9 (`notes/spec-first-study/backend-review-9.md`, on `aa2dcdcac0`) has no first-tier finding.
Round 8's repairs hold: only two contract clauses produce a `Meta` put, and both carry `MW`. `NC`
and `MW` are the same half of the flag, so no token is held twice. Under the stop rule this
increment (rounds 7-9) is done: no first-tier finding came from a repair, and none ran three rounds.

Left from round 9, all second tier:
- **R9-1 and R9-2: docstrings, deferred to the next code change in `InvStore.lean`.**
  - `batchTxSpecG`'s and `isKeyBackendG`'s docstrings should name `MW`.
  - `kbMW`'s docstring should state the cost of `kbMW none := True` (R9-2). The compaction specs
    (`store.Compact`, `updateCompactRev`, `scheduleCompaction`) need `storeCmp`, i.e. mvcc's
    assumed backend. Every such store comes from `NewStore`/`New`/`newWatchableStore`, which take
    the opaque `viewNoCmp` that nothing supplies. So the compaction results hold of no backend
    until the wiring step, and must not be counted as verified until then. This goes to the user
    with question 5.
  - A docstring edit there rebuilds about 1700 modules, so it waits to ride with the next real
    change.
- **R9-1, the trust-base list:** add `MustUnsafeSaveConfStateToBackend`. It writes the confState
  key through its own triple, not a compaction key, so it stays true.
- **R9-3:** `SetScheduledCompact.spec` and `SetFinishedCompact.spec` take a general `MW` at the
  wiring step.

**Before the freeze (the plan's new rule):** `storage.OpenBackend`'s axiom was restated in
`2e49ff1aa9` (its wand dropped; `newPostK` now carries the flag's half), and so was
`OpenSnapshotBackend`'s. Both get the `axiom` skill before Freeze.

Still the user's: question 4 (`BParams.VI`, which blocks `metaReadTx`'s value case) and question 5
(the compaction's tokens at wiring: `storeRT` and now the flag's half, which `store.restore` would
hand to the store instead of consuming `kbNoCmp`).

### `OpenBackend`'s axiom check before Freeze (2026-10-29)

The `axiom` skill (branch `axiom/openbackend`, `notes/axiom-review/openbackend.md`): the restated part
(`fkOwn γ (fkInit D)` in `newPostK`) survives; the axiom was false as documented by an older gap, the
quota's mmap size (a quota above about 2.5·10^14 makes `newBackend` panic in any environment;
`issues/etcd-quota-backend-bytes-mmap-panic.md`). Fixed, the user's decision: `openPre` takes
`storage.openMmapOk cfg`, and it reaches `NewServer.spec`/`specCompact`/`specM` (`"%Hmmap"`, kept in
`srvSnapRO`) and `applySnapshot.specSnap`/`applySnapshot_walk` (`hmmap`). `OpenSnapshotBackend`'s
statement takes it through `openPre`.

## The user's answers to questions 2 and 4 (2026-10-29)

- **Question 2 (R4-2, D22's `viewAt`): option (a), the user's.** The batch lock's quarter of
  `γ.view` moves to the logical view, and `viewAt γ vd := ∃ L, (the batch quarter at L) ∗ thinV γ
  vd L`: a snapshot's view `vd` is the physical one, thin of the logical view by registered
  deletable keys. **For the D22 track (the collaborator's):** `backend.Snapshot`'s spec mentions
  `viewAt`; its text is unchanged, its meaning weaker (exact when nothing is deletable,
  `dlNoDel`). `backend.Snapshot`'s axiom is an axiom-backed spec whose meaning changes: it gets the
  `axiom` skill before Freeze. Unblocks: the limited range's case of the new bridge, and folding
  `Unlock.specC`/`UnsafeDelete.specC` into their specs.
- **Question 4 (the compaction keys' values): on the tracked-absence flag, the user's** (the
  recommendation: three levels, not `BParams.VI`). How it is stated is below ("Question 4's
  statements"), decided by the agent within that choice.

### Question 4's statements (2026-10-29; decided by the agent within the user's choice)

- **The three levels, as a flag and a bit.**
  - `fkOwn γ 0`: no compaction key, the flag as before.
  - `fkV γ true`: only well-formed values. This is a new discarded `dghostVar Bool` (`γ.fkv`),
    persistent.
  - Neither: nothing is known.
  - Why not a third level of the `monoNat`: "only well-formed values" is stable, since a put needs a
    well-formed value. But a reader with no part of the client's exclusive half (the compaction's
    `checkPrevCompactionCompleted`, concurrent with a job that holds it) could not learn an upper
    bound of the flag. A persistent bit, fixed at creation, gives the same three levels and is
    readable by anyone.
- **The values: `BParams.FV`.** It is a new field, defaulting to `fun _ => True`; `KBReal.P` sets
  it to `metaRevVal`. Decided by the agent: a field rather than a backend copy of mvcc's
  `revBytes`, so that the backend does not state mvcc's encoding.
  - The batch lock's ghost (`fkHalf`) and the readers' witness (`fkRd`) carry `fkOk P f w st` /
    `fkOkRv P f w rv`: `f = 0` gives absence, `w` gives well-formed values.
  - The read law is `fkRd_wf`: `fkV γ true ∗ fkRd γ P rv ⊢ ⌜fkWfRv P rv⌝`.
- **Creation.** `newPost`/`newPostK`'s last component is now `fkCl γ P D :=
  fkOwn γ (fkInit D) ∗ fkV γ (fkWInit P D)`. `OpenBackend`'s text is unchanged, but it says more:
  the bit is computed from `D`, in `New`'s proof, so the axiom claims nothing more of the file.
  `bkNoCmp_of_fkOwn` became `bkNoCmp_of_fkCl`, and `fkV_of_fkCl` gives the bit at `true` over data
  without compaction keys.
- **`UnsafePut`'s spec** gains the premise `fkKey bi.name kb → P.FV vb`. Its four callers put
  non-compaction keys (`absurd`), or `metaRevVal` values (`bt_metaPut`, from `metaPutCap`'s premise).
- **`metaReadTx rt RT`.** `RLock` now takes the reader's budget token `RT` and `RUnlock` gives it
  back, as `keyReadSnap`'s do. For mvcc's assumed backend `RT = True` (`isKeyBackendG_cmp`), so
  `checkPrevCompactionCompleted`'s proof is unchanged. Who supplies `storeRT` to it over the real
  backend stays question 5.
- **The new bridge** (`isKeyBackendG_of_backendC`, unwired) takes `hFV : ∀ v, P.FV v ↔ metaRevVal v`
  and the persistent `fkV γ true`. Its `metaReadTx` case is proved (`rt_metaWf`): one `sorry` fewer.
  The wiring step supplies `fkV γ true` from `fkV_of_fkCl`, over data without compaction keys.

### Question 2: recorded, not implemented in this round (2026-10-29)

Implementing option (a) is the plan's "group 2" (R4-2), and it is larger than one repair round.
Measured:
- **The batch lock's quarter of `γ.view` moves to an existential logical view**
  (`∃ L, viewQ γ ¼ (vData P (st.C, st.R)) L`). It is updated in `batchGhostAt`, `batchGhostW`, the
  commit lemmas (`InvCommit`, 150 lines), the allocation, `Unlock`'s write-backs (275 lines) and the
  read side's closes (`ReadSide`, 772 lines), each establishing `thinV` for its new `L`. Then
  `viewAt γ vd := ∃ L, the quarter at L ∗ thinV γ vd L` (`InvSnapshot`).
- **`relog`**: the session's writes over `L`, falling back to `L` only at safe-range keys (R5-1),
  with its laws.
- **The fold** of `Unlock.specC` and `UnsafeDelete.specC`: both are unproved Draft statements, used
  nowhere. They need `Unlock`'s deleting-session branch proved, and `Unlock.spec` has 40 client
  files.
- **The limited range's case** (the last `sorry` of the new bridge) after that: the job's session
  token with its pending deletes, its `Meta` put and its budget (3.1-3.5).

Recommended: a dedicated round, with its own Draft of `relog` and the fold's statement, and a review
before the proofs, since it changes `Unlock.spec`, a statement 40 files use. Until then
`Unlock.specC`/`UnsafeDelete.specC` stay beside their specs, and the limited-range `sorry` stays.

### Review round 10: question 4 closed (2026-10-29)

Round 10 (`notes/spec-first-study/backend-review-10.md`, on `facf2ad1e1`) has no first-tier finding.
It endorses both choices made by the agent: the persistent bit `fkV`, and `BParams.FV`. The
question-4 increment's review is closed. Its full build of record passed (10943 jobs); the trust
check matches the baseline.

Second tier, to go in with the next code change:
- **R10-1:** a law giving `bkNoCmp γ ∗ fkV γ true` from one `fkCl` under `noCmpData D`, plus the bit
  from `fkWfD P D`. Needed at wiring.
- **R10-3:** a line in `notes/axiom-review/openbackend.md` on why `OpenBackend`, `Snapshot` and
  `MustSaveMemberToBackend` stay true with `fkCl`/`fkHalf`. Also R9-1's
  `MustUnsafeSaveConfStateToBackend` entry.
- **R10-2:** stale docstrings: `OpenBackend.lean:17` and `OpenSnapshotBackend.lean:13` still say
  `bkNoCmp_of_fkOwn`; `isKeyBackendG_of_backendC`'s new hypotheses are undocumented; so is
  `isKeyBackendG`'s `RLock` taking `RT`.
- **R10-4:** a restart over a file that records a compaction needs a well-formedness premise on the
  file. The bit never rises.
- **R10-5:** delete the unused `viOk` (`DelKeys.lean:97-101`); the `BParams.VI` sketch is superseded.

Next: question 2's own round (Draft, then Review), then question 5 (the wiring).

## Question 2's Draft round (2026-10-29; option (a), the user's)

**The statements**, in `Proof/go_etcd_io/etcd/server/v3/storage/backend/LogicalView.lean`
(Draft). It is real Lean beside what it replaces, imported by nothing, with every law proved and no
`sorry`. Nothing is switched yet.

- **`relog P L st`**, the logical view after a put session's `Unlock`:
  `sData P st.S ∪ filter (fun nk _ => P.SB nk.1 && (vData P (st.C, st.R)).lookup nk = none) L`.
  - The session's writes go over `L`. `L` is kept only at safe-range keys that the readers'
    physical view already lacked, i.e. keys compaction deleted earlier. Those stay in mvcc's
    logical `Key` bucket (R5-1).
  - A key the session itself deleted leaves the logical view as well.
  - Refinement of R4-2's sketch (decided by the agent): the sketch fell back at every safe-range key
    missing from `S`, which would undo the session's own deletes. This version needs no new premise
    on the put branch.
  - Laws, all proved: `relog_lookup`, `relog_exact` (an exact `L` gives `sData P st.S`), `thinV_relog`
    (the old physical view thin of `L` gives `sData P st.S` thin of `relog P L st`), `thinV_trans`.
- **`batchViewQ γ P st := ∃ L, viewQ γ ¼ (vData P (st.C, st.R)) L`**, the batch lock's quarter over
  the logical view: `batchGhostAt`'s first conjunct after the switch.
  - Today's exact quarter is an instance (`batchViewQ_of_exact`).
  - The clients' share agrees with it (`batchViewQ_bView`: the physical view is thin of what a client
    holds).
  - `batchLocked_thin`, the law the bridge reads, is stated and proved today. It is re-proved over
    `batchViewQ` at the switch.
- **`viewAtL γ vd := ∃ L, viewQ γ ¼ vd L`**, D22's `viewAt` over the logical view (option (a)). It
  replaces `viewAt` at the switch.
  - Today's `viewAt` is an instance (`viewAtL_of_viewAt`), so `backend.Snapshot`'s observation only
    gets weaker.
  - With `dlNoDel` it is today's `viewAt` (`viewAtL_noDel`; D22's users never compact).
- **`backend.batchTxBuffered.Unlock.specF`**, the folded `Unlock` spec, one spec for both kinds of
  session:
  - **A deleting session:** `thinV γ (sData P st.S) (vData P (st.C, st.R))`, no puts to the non-hook
    buckets in the write buffer, `W ∗ Pk ∗ Q`. The logical view stays. This is today's `specC`
    branch. Today's `viewSame` branch is its instance (`viewSame_thin`).
  - **A put session:** `∃ vd, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q)`. Today's
    `spec` had `sData P st.S` in place of `relog P vd st`.
  - **Today's `spec` is a corollary under `dlNoDel`** (`Unlock.spec_of_specF`, proved). It is the
    old bridge's and D22's route; they never compact.
  - At the switch `spec := specF`; `specC` and `specF` go.
  - Still to add: the no-change branch alone, without `dlNoDel` (`SetTxPostLockInsideApplyHook`), as
    a one-line corollary through `viewSame_thin`.
- **`UnsafeDelete.specC`** is already the folded `UnsafeDelete` statement: any bucket, with `dlIs` at
  a safe-range key, and `own` choosing between a key slice and a key read from the transaction. At
  the switch `spec := specC`. Its old callers pass `own := true`, and their `P.SB = false` reduces
  the `dlIs` conjunct to `True`.

**Who decides.**
- `viewAt` is the only change to a trusted statement's meaning. It goes into `backend.Snapshot`'s
  axiom spec, D22's (the collaborator's), and only weakens the caller's observation. It is the
  user's option (a). It gets the `axiom` skill before Freeze, as already recorded.
- `Unlock.spec` and `UnsafeDelete.spec` are proved backend specs. Their text is visible only as
  hypotheses passed through by `StoreBackend`, `BuildLemmas`, `SnapApplyWalk`,
  `EtcdServer.applySnapshot`, `NewServer` and the links, none of them top-level statements. No new
  family: `specC` and `specF` disappear.
- No question for the user this round.

**Proof sites at the switch** (measured with `etc/importers.py` and grep, no build):
- **The batch quarter** (`batchGhostAt := batchViewQ ∗ …`, `InvBackend.lean`; rebuilds 2120
  modules). Mentions of the quarter or `batchGhostAt` per file:
  - `InvBatch` 16: the session steps keep `(C, R)`, so they are mechanical;
  - `ReadSide` 8: `rtRes_wb_close`, and `rtRes_cm_close`'s window, where the readers' quarter and
    the batch's take the same `L`;
  - `InvCommit` 6: a commit keeps `L` (`thinV_rebase`);
  - `InvBackend` 6;
  - `batchTxBuffered__Unlock` 4;
  - `NewAlloc` 3: initially `L` is exact;
  - `batchTx__lock` 2, `InvSnapshot` 2;
  - `DelKeys`, `InvNew`, `UnsafePut`, `UnsafeSeqPut`, `safePending` 1 each.
- **`Unlock`'s proof:** the deleting branch is new, from `specC` (about 200 lines). The put branch's
  write-back sets every quarter to `relog P vd st`, including the readers' quarter inside
  `readTx.mu`, in the write-back's close.
- **`UnsafeDelete`'s proof:** a safe-range delete with `dlIs` (`safeSt` no longer needs the committed
  keys in the writer's contents; round-1 repairs).
- **Callers**, all in `BackendBridge.lean` plus one backend hook. No server or example proof applies
  `Unlock`/`UnsafeDelete` directly; they pass the specs through. Earlier "40 files" estimate:
  `batchLocked`'s users, not `Unlock`'s.
  - `bt_unlock`, `bt_unlockD`: put branch; the old bridge goes through `spec_of_specF`, the new one
    uses `relog`.
  - `bt_unlock0`, `bt_unlockO`, `bt_unlockOAt`, `SetTxPostLockInsideApplyHook`: no-change branch,
    via `viewSame_thin`.
  - `bt_leaseDel`: `UnsafeDelete` with `own := true`.
- **Then the limited-range case of the new bridge** (its last `sorry`).
  - The job's session must give `Unlock`'s deleting branch `thinV (sData P st.S) (vData P (st.C,
    st.R))`, so its session token should record that its deletes are registered.
  - That is a statement inside mvcc's contract (the limited-range clause), the agent's to word.
- **Estimate:**
  - about 500 changed lines over the 12 backend files;
  - about 200 for `Unlock`'s deleting branch, about 100 for `UnsafeDelete`;
  - about 60 in the bridge, about 300 for the limited range;
  - one full build per round, rebuilding about 2100 modules.

### Question 2's switch (Prove, 2026-10-29)

The reviewed Draft (round 11, no first-tier finding) switched in, with round 11's findings applied:
- **The batch lock's quarter is over the logical view**: `batchGhostAt`'s and `batchGhostW`'s first
  conjunct is `batchViewQ γ P st` (`∃ L, viewQ γ ¼ (vData P (st.C, st.R)) L`, `InvBackend.lean`).
  `viewAt` (D22's, `InvSnapshot.lean`) is the same quarter at a physical view `vd`
  (`∃ L, viewQ γ ¼ vd L`), the user's option (a); `backend.Snapshot`'s axiom's docstring says so, and
  it gets the `axiom` skill before Freeze.
- **R11-1** (decided by the agent; internal specs): `batchTxBuffered.commit.spec` and `unsafeCommit.spec`
  take a target `L'` and, out of a window, `thinV γ (sData P st.S) (vData P (st.C, st.R))` (was: the
  view unchanged), in a window `thinV γ (sData P st.S) L'` (was: none), and give the clients' view back
  at `L'` (was: the new physical view). `rtRes_cm_close` and `rtRes_wb_close` (`ReadSide.lean`) the same
  way; `Commit`, `CommitAndStop`, `run` pass the exact instance (`thinV_refl`).
- **R11-2**: a put session that commits opens its window at the exact new physical view and the
  commit's close moves it to `relog`; one that does not commit moves the view to `relog` at the
  write-back's close.
- **`Unlock.spec` is the folded statement** (Draft's `specF`; `spec`, `specC`, `specF` and
  `spec_of_specF` gone). Its proof covers the deleting branch (the write-back leaves the readers' view,
  the commit's new physical view thin of the old) and the put branch through `relog`.
- **`UnsafeDelete.spec` is the Draft's `specC`** (any bucket, `dlIs` at a safe-range key, `own`); its
  proof needs no "not safe-range" premise any more (`sessWf_del`).
- **R11-3**: the bridge's `bt_seqPut`, `bt_unlock`, `bt_unlockD`, `bt_range` are proved once over the thin
  view (`batchLocked_thin`, the new `keyView_sub`), shared by both bridges; `batchLocked_view` is gone.
  `bt_range` takes `□ (∀ k, dlIs γ (key, k) -∗ Del k)` (the old bridge's from `dlNoDel`, the new one's
  `bkDel`). **R11-4**: `keyView_relog`, the put session's view after `Unlock`. **R11-5**: `relog` without
  the `P.SB` filter (`relog_same`: a session that changed nothing keeps its logical view). **R11-6**:
  `relog`'s docstring. **R11-7**: `backend__Snapshot.lean`'s docstring.
- `LogicalView.lean` (the Draft module) is gone: its statements are in `InvBackend.lean`,
  `InvSnapshot.lean` and the specs.

Left: the new bridge's limited-range `sorry` (the job's session token must record that its deletes are
registered, so that `Unlock`'s deleting branch gets its `thinV`), and round 10's doc items R10-2/R10-5.

### Review round 12 and its repairs (2026-10-29)

Round 12 (`notes/spec-first-study/backend-review-12.md`, on `f175d283b5`): one first-tier finding,
in the Draft round 11 passed (not churn from round 11's repairs). Repairs, decided by the agent:
- **R12-1:** `UnsafeDelete.spec`'s premise `dlIs` at a safe-range key, which nothing used (`Unlock`'s
  deleting branch asks for the whole `thinV` again), dropped with its docstring sentence (option
  (a)); the spec only gets stronger. Whether the job's session should carry the registration
  instead (option (b)) is for the limited-range glue to decide.
- **R12-2:** laws `thinV_sub`, `thinV_dl`, `relog_congr` (`InvBackend.lean`); the bridge's five unfolds
  of `thinV`/`relog` (and `keyView_thin`'s) are uses of them.
- **R12-3:** `viewAt_bView` (the snapshot's physical view thin of the clients' view) and
  `viewAt_noDel` (with nothing deletable, the quarter at `vd` itself), both true and proved
  (`InvSnapshot.lean`, now importing `DelKeys`).
- **R12-4:** `keyView_thin`'s first half is `keyView_sub`.
- **R12-5:** `rtRes_cm_close`'s docstring and `ReadSide.lean`'s header; the `Snapshot` spec's header
  (D22's file, docstring only: `D` reads thin of the readers' logical view; STATUS says so).
- **R12-6:** a note (out of a window `L'` is unused).
- **Before Freeze, the `axiom` skill on `backend.Snapshot`:** include round 11's four commit cases, and
  the put window's "`W` from the wand at the commit's close".


## The limited range proved; round 13's and round 10's items (2026-10-29)

**The new bridge has no `sorry` left.** `isKeyBackendG_of_backendC`'s compacting range is
`bt_rangeC` (`BackendBridge.lean`).

**Decided by the agent.**
- **Where the registered deletes are recorded: in the token, R12-1's option (a) kept.** The job's
  token is `bkLockedC γ P b tx n`:
  - the batch lock held at the range's write transaction `tx`;
  - the writer's contents off the hook's buckets thin of the readers' view (`thinV`, which holds
    the registrations);
  - nothing buffered off the hook's buckets, out of the hook's window, room for `n` operations and
    a commit's hook;
  - a write-back's budget.
  - Each step keeps it: deletes of registered keys (`thinV_delKey`) and compaction-key puts into
    `Meta` (`sData_insert_HB`, `wbNoKey_putHB`, the flag's half given back).
  - `Unlock`'s first branch takes it.
  - So no backend statement changed, and R12-1's option (b), the session recording its deletes, is
    not needed.
- **The range's slices.** They are read under the token through `batchLocked_rdB` and a new backend
  law, `batchLocked_rdB2`: two at once, half of bbolt's transaction each (`rdB_acc`), for `rdCap2`.
- **R10-1's laws go in mvcc's `Image.lean`, beside `bkNoCmp_of_fkCl`.**
  - `bkNoCmp_fkV_of_fkCl`: both from one `fkCl` under `noCmpData D`.
  - `fkCl_wf`: the half and the bit under `fkWfD P D`.
  - Not in the backend, which has no lemma file over `fkCl` yet.
- **R13-2 not done.** It would move `viewAt` into `InvBackend.lean` and define `batchViewQ` through
  it: cosmetic, and it moves a D22 definition. `viewAt_bView` and `batchViewQ_bView` stay two short
  laws.

**Done:**
- **R13-1, R13-3:** the dead `hSB`; the unused import.
- **R10-2:** docstrings of `OpenBackend` and `OpenSnapshotBackend` (`bkNoCmp_of_fkCl`, the bit), of
  `isKeyBackendG` (`metaReadTx`'s `RLock` takes `RT`), and of `isKeyBackendG_of_backendC` (its
  cases, `hFV`, `fkV γ true`).
- **R10-5:** the unused `viOk` deleted from `DelKeys.lean`. The `BParams.VI` / `viOk` / `metaVI`
  sketch above (sections 2-3) is superseded by question 4's `BParams.FV` and the bit `fkV`.

**Left:** the wiring (question 5, the user's), then Test, Probe, Freeze (with the `axiom` skill on
`backend.Snapshot`, running on branch `axiom/snapshot`) and Prove.

## Question 5: the wiring, the user's decisions (2026-10-29)

The user approved the recommendations (2026-10-29):
- **(i) The read token.** `store.Compact.spec` borrows `storeRT γ` from the apply thread's
  `writerOwn` (pre and every post branch), for `checkPrevCompactionCompleted`'s `metaReadTx rt RT`.
- **(ii) The write right stays in the store.** `store.restore` stops consuming `kbNoCmp`: after its
  two reads it keeps the flag's half (`kbMW`) in the store's own state. It never goes back to a
  client.
- **(iii) The assumed backend's flag.** `kbMW none` becomes an opaque `viewFk γb`, mirroring
  `viewNoCmp`, so results over mvcc's assumed backend can be met by an honest creator.
- **(iv) Compaction on.** The real backend gets `kbCmp := True` through the sorry-free
  `isKeyBackendG_of_backendC`, with R2-7's D22-side changes and R9-3 (`SetScheduledCompact`/
  `SetFinishedCompact` with a general `MW`). The old bridge becomes an instance of the new one, the
  last variant.
- **Narrowed after review round 14 (the user's, 2026-10-29):** (iv) is now Q5-1's mode in the instance
  (`kbCmp (some d) := d.cm`), with the server's side (R2-7's D22 change, `NewServer.spec`) deferred to
  M2. See "Question 5's Draft, repaired after review round 14", which supersedes the Draft round's
  design and lists below where they differ.

### Question 5's Draft round (2026-10-29)

Draft statements: `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/WiringDraft.lean`. It is imported by
nothing and builds. Its one law (`kbNoCmpW_MW`) is proved; the switch's two laws are stated as
`Prop`s (`isKeyBackendG_weaken.stmt`, `isKeyBackendG_congrDel.stmt`), not assumed.

**The design.**
- **(ii), where the write right lives: the batch lock's resource** (decided by the agent).
  - `storeWW s γ := storeW s γ ∗ kbMWW γ.kb γ.bucket`. `store.restore`'s post gives the half back
    (`kbNoCmpW_MW`). `NewStore` deposits it with `W` at its first `Unlock` (the late-bound `lateW`
    for the real backend, `writerRes` for the assumed one).
  - Every session that writes a compaction key takes it from the lock's resource and returns it at
    its `Unlock`: `store.Compact`'s `SetScheduledCompact`, and the job's `UnsafeSetFinishedCompact`.
  - Why not the compaction right or token: `store.Compact`'s `SetScheduledCompact` runs while the
    previous job may be running `UnsafeSetFinishedCompact` (Go: the job is asynchronous). An
    exclusive right in the token, which the queue hands from job to job, could not be in both
    places. The batch lock already serializes them.
  - So `store.restore`'s post gains `kbMW…`; its callers (`NewStore`, `store.Restore`) take it.
    `store.Restore` (D22's, a received backend) drops it: no compaction on a server that installs
    snapshots.
- **(iii)** `viewFkW γb f` is opaque, with `viewNoCmpW γb := viewFkW γb 0` and
  `kbMWW none γb := ∃ f, viewFkW γb f`. `kbMW` takes the bucket's name `γb`. Uses:
  `storeBackend`/`storeBackendT`/`physOk`, the `#Hbt` facts, `batchTxSpec` (about 10, all in mvcc).
- **(iv) The job's budgets go in the compaction token** (decided by the agent).
  - `compactTokW γ c := (∃ c' ≤ c, idxCompactor γ.idx c') ∗ compactJobRes γ.kb`: a reader's token,
    the safe-range slot, the write-back supply, handed from job to job through the queue.
    `NewStore` takes `compactJobRes kb` from its caller (all `True` for the assumed backend).
  - `storeBackend`'s `SR`/`SRh` become `kbSR γ.kb` and a new `kbSRh γ.kb` (`srHeld`).
- **(iv) The registration.** A compacting store fixes the backend's deletable keys to its index's
  `delKey` (`storeDlReg γB γi`, over `delKeyI γi`, since `delKey γ = delKeyI γ.idx`). The creator can
  do this before `NewStore`, because the index's names `γi` are allocated first (`NewStore_backend`,
  `BuildLemmas`). The store's `Del := delKey γ` then comes from the bridge's `bkDel` through
  `isKeyBackendG_congrDel` (stated with `◇`, `delKey` being timeless).
- **(iv) The old bridge** becomes `isKeyBackendG_of_backendC` followed by `isKeyBackendG_weaken`: a
  contract with `Cmp := True` and no deletable keys (`dlNoDel`) is one with any `Del'`, no
  compaction, and trivial slots. One proof; `isKeyBackendG_of_backend` becomes a corollary, used by
  D22's exact readers.
- **R2-7, D22's side** (approved with (iv); statement for the switch). `NewServer` gives
  `kbWTSupply (some d)` from `srvWTPool`'s invariant at the boot backend `d`:
  `srvWTPool E γp ∗ dghostVar E.γbe DFrac.discard d ⊢ □ (⧗ 1 ={⊤}=∗ wbTok d.γB)`. The server in
  compaction mode discards its fraction of `E.γbe` at boot: no snapshot is ever installed, so `d`
  is fixed. Each conversion adds the receipt to the pool's `a` and takes one of its `n` tokens, so
  `receiptBound ≤ a + n + 1` is kept, with `wbInit`'s split shared.
- **R9-3:** `SetScheduledCompact.spec`/`SetFinishedCompact.spec` take a general `MW`, not
  `kbMW none`.

**Statement changes, by kind.**
- **Seen by mvcc's clients:**
  - `store.Compact.spec`: `storeRT γ` in the pre and every post branch (`store.Compact.specW`).
  - `NewStore.spec`: `kbNoCmpW kb γb`, `compactJobRes kb` in the pre; same post (`NewStore.specW`).
    `New.spec` and `newWatchableStore.spec` follow, with the same additions.
  - `store.restore.spec`: its post gains `kbMW…` (private to mvcc, but a `Spec` file).
  - `kbMW`/`kbNoCmp`/`kbCmp`/`compactTok`/`storeW`: definitions in their statements.
- **Exported results:**
  - `mvcc_NewStore_backend` and `NewStore_backend`: `dlInit` fixed by the store, `fkV d.γB true`
    (from `newPost`'s `fkCl`), `compactJobRes (some d)`, three more callee specs (`LockFor…`,
    `UnlockFor…`, `UnsafePut`), and `d.P`'s `hHK`/`hFV`. Same post; the docstring's "the compaction
    is of no use" goes.
  - `mvcc_backend_bridge`, `mvcc_storeBackend_of_backend`: over the new bridge.
  - `mvcc_store_Compact`: same text, (i)'s meaning.
  - `server_kv_backend`, `server_kv_watchable`, `server_kv_backend_hooks` (`etcdserver/Results.lean`):
    the same pre additions as `NewStore_backend`.
  - `NewServer.spec`: through `BuildLemmas`; it supplies `compactJobRes` from `srvWTPool` (R2-7) and
    `fkV` from `newPost`.
  - `putgetc`: unaffected until M2 resumes and uses the compaction over the real backend.
- **Trusted:** none changed, unless Q5-2 below.
- **D22's (the collaborator's):** `srvWTPool` (R2-7's conversion, the discarded `E.γbe`);
  `store.Restore` (drops the returned write right); `RestorePre` (`kbNoCmp`); `SnapApplyWalk`/
  `SnapApplyDefs` (Q5-1).

**Proof sites** (`etc/importers.py`, no build):
- mvcc:
  - `InvStore.lean` (the definitions, about 10 uses of `kbMW`), `InvCompact.lean` (`compactJobPre`
    drops `storeCmp`, takes the token's budgets);
  - `store__restore.lean` (return the half: small), `NewStore.lean` (deposit the half at the first
    `Unlock`, the budgets into the token), `store__Compact.lean` (thread `storeRT` to
    `checkPrevCompactionCompleted`; the half for `SetScheduledCompact` from the lock);
  - `store__scheduleCompaction.lean` (the job: the half from the lock in its last batch, the budgets
    from the token), `store__updateCompactRev`/`compactLockfree`/`checkPrevCompactionCompleted`
    (`storeCmp` only), `store__Restore.lean`, `newWatchableStore.lean`, `New`;
  - `BackendBridge.lean` (`isKeyBackendG_weaken`, `isKeyBackendG_congrDel`), `StoreBackend.lean`,
    `Results.lean`, `Link.lean`.
- etcdserver: `BuildLemmas.lean`, `Results.lean`, `InvApplier.lean` (R2-7), `SnapApplyWalk.lean`,
  `SnapApplyDefs.lean`, `RestorePre.lean`.
- Estimate: about 700-900 lines: mvcc about 450, the two laws about 180, etcdserver/D22 about 200.
  One full build per round, since `InvStore` rebuilds 1723 modules.

**Questions for the user** (beyond the approved (i)-(iv)):
- **Q5-1: `kbCmp := True` for every real backend, or the mode in the instance.**
  - The conflict: a store whose backend is fixed at "nothing deletable" (`dlNoDel`) cannot meet
    `Cmp := True`, because the job's deletes need the backend's registration to give `delKey`. Today
    every real store is fixed at `dlNoDel`, and D22's exact readers depend on it: `SnapApplyWalk`
    fixes the received backend at `dlNoDel`, and `store.Restore` over it builds the store's contract.
  - (a) **The mode in the instance** (recommended): `KBReal` gains `cm : Bool` (the server's
    `ρ.kv.cmp`, M2's mode), `kbCmp (some d) := d.cm` (`kbCmpM` in the draft).
    - A compacting store registers `delKeyI`; the others, and D22's received backends (`cm := false`
      in `SnapApplyDefs`' records), keep `dlNoDel` and the old bridge, an instance of the new.
    - One spec per function, with the mode in the state.
    - D22's statements change only by the record field.
  - (b) **Literally `kbCmp := True`**: every real store registers `delKeyI`. D22's exact readers get
    exactness from "no compaction ever" (`crevFrozen` makes `delKeyI` false) instead of `dlNoDel`.
    That is a restatement of D22's readers (F7), the collaborator's statements.
- **Q5-2: the safe-range slot's supply grows a trusted statement's meaning.**
  - The job's budget `compactJobRes` includes the slot `srSlot d.be` (ownership of the backend's
    `safeRangeDeleteMu`). No creation path gives it today.
  - `New`'s post (`newPost`/`newPostK`) would gain it: proved from the zero `RWMutex` that
    `newBackend` allocates. `storage.OpenBackend`'s text is `newPostK`, so its meaning grows (still
    "does what `New` does").
  - Under the Freeze rule, it then gets the `axiom` skill's check again (cheap: the claim is `New`'s
    proved post).

### Question 5's Draft: the user's answers (2026-10-29)

- **Q5-1: the mode is in the instance.** `KBReal` gains `cm : Bool` (M2's `ρ.kv.cmp`), and
  `kbCmp (some d) := d.cm` (the Draft's `kbCmpM`). A compacting store registers `delKeyI`. Every
  other store, and D22's received backends (`cm := false`), keeps `dlNoDel` and the old bridge as
  an instance of the new one. D22's statements don't change. This replaces "(iv): `kbCmp := True`
  for the real backend".
- **Q5-2: the slot comes from creation.** `newPost`/`newPostK` gain the safe-range slot `srSlot`,
  proved in `New` from `newBackend`'s zero `RWMutex`. `storage.OpenBackend`'s text is unchanged,
  but its post now means more, so the `axiom` skill runs on it again before Freeze.

Next: Review of the Draft with these answers, then the switch.

### Question 5's Draft, repaired after review round 14 (2026-10-29)

Review round 14 (`notes/spec-first-study/backend-review-14.md`) had seven first-tier findings (F1-F7).
The Draft (`WiringDraft.lean`) is repaired; still no proof switched. Checked: `etc/lean-check.py -a`
and a targeted `lake build --packages` of `mvcc.WiringDraft` (2311 jobs), both pass.

**The user's answers (2026-10-29).**
- **F2: the job's reader token comes from the store's own pool, only in compaction mode.**
  `NewStore` keeps back `nJobRd kb cm` readers: one for a compacting real store, else none. So
  non-compacting stores, D22's backends and the server keep their exact reader counts.
- **Defer the server's side to M2.** R2-7's D22-side change and `NewServer.spec`'s change leave this
  stage. The server stays `cm := false`, and M2 turns compaction on in the server.

**Repairs** (decided by the agent unless marked):
- **F1, the write right's home** (decided by the agent; option (a) of the review, within the user's
  (ii)).
  - `writerRes` gains `mwSlotW γ cm γmk`: the lock key `mwKeyW` when the store compacts, else nothing.
    It is deposited with `writerRes` at `NewStore`'s first `Unlock`, before `restore`.
  - After `restore` gives the half back (`kbNoCmpW_MW`), `NewStore` allocates
    `mwInvW γ γmk := inv mwN (kbMWW γ.kb γ.bucket ∨ mwKeyW γmk)`. It goes in `isStore` at the switch.
  - A session that writes a compaction key holds the batch lock, so it holds the key. It swaps the
    key for the right, writes, and swaps back (`mwSwapW W MW := □ (W ={⊤}=∗ MW ∗ (MW ={⊤}=∗ W))`;
    the law `mwSwap_of_inv.stmt`).
  - The lock's resource `W` stays `storeW` (for the real backend, `lateW d.gx` from creation). The key
    is inside `writerRes`, which `lateW` registers.
  - The key's name is a new physical name (`PhysNames.mk`), allocated by `NewStore`, or by
    `store.Restore` for its new names. D22's statements keep their text.
  - The plan's earlier "`store.Restore` drops it" is superseded. A restored store's `writerRes` holds
    the key only if it compacts, which it does not (see the question below).
  - Option (b), D22's pending-deposit pattern, was rejected: it touches D22's `writerReg`.
- **F2/F3, the budgets by the mode.**
  - `compactJobResM kb cm` is `kbRT ∗ kbSR` for a compacting real store, else `True`. Its reader
    token comes from `NewStore`'s pool.
  - `NewStore` takes the slot from its caller only in compaction mode (`kbSRM`).
  - `compactTokW γ cm c := (∃ c' ≤ c, idxCompactor γ.idx c') ∗ compactJobResM γ.kb cm`.
- **F4.** `NewStore.specW`'s contract premise is now at `γ.idx = γi`.
- **F5, the write-back supply** (the reviewer's preference): `kbWTSupplyM kb cm`, persistent.
  `NewStore` takes it (`□ kbWTSupplyM kb cm`) and keeps it in `physOk`. `store.Compact` and the job
  pay from the receipts of their own steps. `store.Compact.specW`'s pre gets no `storeWT`.
- **F6.** `SetScheduledCompact.specW` and `SetFinishedCompact.specW` are over `batchTxSpecG` in full
  generality: `RT`, `WT`, `PutOk`, `Rb` and `MW` are the caller's, `Cmp := True`, and they take
  `mwSwapW W MW`. Their pre has `RT ∗ WT`, their post `RT`.
- **F7.** `isKeyBackendG_weaken.stmt` concludes at any `SR' SRh' MW'`.

**One question for the user (Q5-3).** Gating the budgets by `d.cm` leaves one gap:
- `store.Restore.spec` (D22's) builds the new store for an arbitrary received record `d'`.
- If `d'.cm` were `true`, its new store's closer (`compactQueue`, `compactTokW`) would need the job's
  budgets: the slot and the write-back supply. `Restore`'s pre has neither.
- The server's own records (`SnapApplyWalk`, `SnapApplyDefs`) will be built with `cm := false`, but
  the spec quantifies over every `d'`.
- Options:
  - **(a) Recommended.** `store.Restore.spec` gains the pure premise `⌜d'.cm = false⌝` ("no restore in
    compaction mode", M2's scope restriction). Its callers discharge it from their literal records.
    This is a one-line change to a D22 statement (the collaborator's).
  - **(b)** No D22 change. A persistent mode witness `cmpOn γ` from `NewStore`'s post becomes a premise
    of `store.Compact.spec`. The token's budgets become `compactJobResM ∨ cmpOff γ`, which `Restore`
    allocates. It is heavier, and it adds a client-visible premise to `store.Compact`.
- The Draft is written for (a); (b) changes only `compactTokW` and `store.Compact.specW`.

**Statements that change** (new text; Lean in `WiringDraft.lean` where marked):
- **Client-visible (mvcc):**
  - `store.Compact.spec`: `storeRT γ` in the pre and in every post branch (`store.Compact.specW`).
  - `NewStore.spec` (`NewStore.specW cm`):
    - the pre takes `kbNoCmpW kb γb`, the contract at `γ.idx = γi`, `kbSRM kb cm` and
      `□ kbWTSupplyM kb cm`;
    - the post gives back `replicate (actualMaxReaders - nJobRd kb cm) (storeReaderC s γ)`.
  - `New.spec` and `newWatchableStore.spec`: the same pre additions. Their posts' reader counts drop
    by `nJobRd kb cm` (`watchReader … - 2 - nJobRd kb cm`).
  - `store.restore.spec`: its post gives the half back, `kbMWW γ.kb γ.bucket` (from `kbNoCmpW_MW`).
  - `SetScheduledCompact.spec` and `SetFinishedCompact.spec`: `SetScheduledCompact.specW` (F6).
  - `store.updateCompactRev.spec`: its `batchTxSpec` facts become the store's `batchTxSpecG` ones, and
    it takes `mwSwapW (storeW s γ) (kbMWW γ.kb γ.bucket)` from `isStore`. Its text changes only in
    what it unfolds; no new premise for the caller.
- **Exported results:**
  - `mvcc_NewStore_backend` and `NewStore_backend`:
    - the pre gains `kbSRM (some d) cm`, `□ kbWTSupplyM (some d) cm`, `fkV d.γB true`, and `dlInit`
      fixed by the store: `storeDlReg d.γB γi` when `d.cm`, `dlNoDel` otherwise;
    - three more callee specs: `LockForSafeRangeDelete`, `UnlockForSafeRangeDelete`, `UnsafePut`;
    - `hHK`/`hFV` for `d.P`;
    - the post's reader count drops by `nJobRd`.
  - `mvcc_backend_bridge` (generic `P`), `mvcc_storeBackend_of_backend` and `storeBackendT_of_backend`:
    over the new bridge, they gain `hHK : ∀ k, metaCompactKey k → P.HK metaName k = false`,
    `hFV : ∀ v, P.FV v ↔ metaRevVal v` and `fkV γ true`, plus the three callee specs.
  - `mvcc_store_Compact`: `storeRT γ` in the pre and post.
  - `server_kv_backend`, `server_kv_watchable` and `server_kv_backend_hooks`: they gain `fkV d.γB true`
    (from `bkNoCmp_fkV_of_fkCl`) and the inherited bridge premises. Their reader counts are unchanged
    (`cm := false`).
  - Not in this stage: `NewServer.spec` (deferred to M2).
- **Trusted:** `storage.OpenBackend`, by Q5-2 only (`srSlot` in `newPost`/`newPostK`; the `axiom` skill
  again before Freeze).
- **D22's (the collaborator's):** only `KBReal`'s new field (`cm := false` in `SnapApplyWalk` and
  `SnapApplyDefs`); `store.Restore.spec` only if Q5-3 (a).

**Proof sites** (`etc/importers.py`; minus the deferral):
- `InvStore`: `KBReal.cm`, `kbCmp`, `kbMW`, `compactJobRes`, `compactTok`, `writerRes`, `physOk`,
  `isStore`, `storeBackend` and `storeBackendT`.
- `InvCompact`; the `store__restore`, `NewStore`, `store__Compact`, `store__updateCompactRev`,
  `store__scheduleCompaction` and `store__compactLockfree` proofs.
- `SetScheduledCompact`, `SetFinishedCompact`, `UnsafeSetScheduledCompact` and
  `UnsafeSetFinishedCompact` (specs and proofs).
- `store__Restore` and `RestoreMoves`; `newWatchableStore`, `New`, `BackendBridge` (the two laws),
  `StoreBackend`, `Results`, `Link`.
- etcdserver: `BuildLemmas`, `Results`, `SnapApplyWalk`, `SnapApplyDefs` and `SnapApplyOpen` (only
  the literal `cm := false` and `fkV`).
- Gone with the deferral: `InvApplier` (R2-7) and `NewServer`.

**Estimate:** about 1100–1400 lines. The deferral takes about 150–200 off the reviewer's 1200–1600.
One full build per round (1724 modules).

**Q5-3, the user's answer (2026-10-29):** (a). `store.Restore.spec` gains the pure premise
`⌜d'.cm = false⌝` (M2's "no restore in compaction mode"); its callers discharge it from their literal
records. This is a one-line change to a D22 statement, so the collaborator will find it here and in
STATUS. The Draft is written for (a).

### Question 5's Draft, repaired after review round 15 (2026-10-29)

Review round 15 (`notes/spec-first-study/backend-review-15.md`) is the increment's second round. It had
three first-tier findings: N1, N2 and N3. N1 is churn from round 14's F1 repair; N2 comes from F2's
repair combined with Q5-3's scope. The Draft (`WiringDraft.lean`) is repaired, and still no proof is
switched. Checked: `etc/lean-check.py -a` and a targeted `lake build --packages` of `mvcc.WiringDraft`.
Under the stop rule, round 16 is the increment's third round.

**The user's answer to Q5-4, (a) (2026-10-29): no restore in compaction mode, for the old store
too.**
- `store.Restore.spec`'s pre becomes `⌜∃ d, γ.kb = some d ∧ d.cm = false⌝ ∗ ⌜d'.cm = false⌝`, which
  extends Q5-3's premise.
- `InvApplier`'s three pure facts `∃ d, E.γ.kb = some d` (`:478`, `:554`, `:830`) each gain
  `∧ d.cm = false`. They hold at boot (the literal record) and after `Restore` (`d'.cm = false`).
- Both are changes to D22 statements, a few lines each. They are M2's scope restriction, stated
  where it applies.

**Repairs** (decided by the agent):
- **N1: the key is the lock's half of a boolean ghost variable.** Round 14's invariant needed an
  exclusive right, and the right is not exclusive: two `fkOwn` halves combine, and `viewFkW` is opaque.
  - `mwKeyW γmk := ghostVar γmk ½ true`.
  - `mwInvW γ γmk := inv mwN (∃ b, ghostVar γmk ½ b ∗ if b then kbMWW γ.kb γ.bucket else True)`.
  - The halves agree on where the right is.
  - `mwSwapW W MW := □ (W ∗ £ 1 ={⊤}=∗ MW ∗ (MW ={⊤}=∗ W))` gained a later credit. The invariant's
    contents are under `▷`, and the assumed backend's opaque flag is not timeless. The sessions get the
    credit from their own steps (`wp_auto_lc`).
  - `mwSlotW`'s gating and `SetScheduledCompact.specW`'s text are unchanged.
  - **Glue, proved:** `mwSwap_of_inv : mwInvW γ γmk ⊢ mwSwapW (mwKeyW γmk ∗ R) (kbMWW γ.kb γ.bucket)`.
- **N3: the invariant lives in `physOk`, not `isStore`.** `isStore_withPhys` is `rfl`, and D22 relies
  on it.
  - New draft `physCmpW s γ cm γmk := if kbCmpM γ.kb cm then mwInvW γ γmk ∗ storeRegd s γ ∗ kbWTSupply
    γ.kb else True`.
  - `storeRegd` comes back into `physOk`, gated: the swap from `storeW` needs it for the real backend,
    and a compacting store is never restored, so it never has a pending registration.
  - `NewStore` has `storeRegd` from `storeW_register` at its first `Unlock`.
  - The switch's law is stated: `mwSwap_of_physOk.stmt`, `physCmpW s γ cm γmk ⊢ mwSwapW (storeW s γ)
    (kbMWW …)` when compacting.
  - F5's supply moved into `physCmpW`.
  - `PhysNames.mk` (and `StoreNames.mk`) is the key's name. Under Q5-3 and Q5-4, `store.Restore`'s new
    names need no fresh key: `mwSlotW` is `True` for them.
- **N4.** `server_kv_backend`, `server_kv_watchable` and `server_kv_backend_hooks` gain
  `(hcm : d.cm = false)`. Their posts give `actualMaxReaders` readers, which holds only when not
  compacting; their caller builds `d` with `cm := false`.
- **N5: the job's reader leaves the pool in `poolBody`'s sum.**
  - Draft `poolSumW kb cm := nReaders - nJobRd kb cm`. This is a D22 definition, so no statement text
    changes.
  - This is preferred over `NewStore`'s `retiredAt γ (nJobRd kb cm)`, which would change statement
    text.
  - **Glue, proved:** `restore_noCmp`. Under Q5-4's premise:
    - `nJobRd = 0` and `poolSumW = nReaders`, so `restore_switch`'s count and `Restore`'s `nReaders - 1`
      are unchanged;
    - `compactJobResM`, `mwSlotW` and `physCmpW` are all `True`.
- **F5's redundant `□`** is dropped from `NewStore.specW` (`kbWTSupply (some d)` is already `□ …`).
  `mvcc_NewStore_backend`'s docstring is to say that its compaction-mode premise
  (`kbWTSupplyM (some d) cm`, `cm = true`) is discharged only by M2 (R2-7).

**Changed statements**, updated from round 14's list:
- **Client-visible (mvcc).** As listed after round 14, and:
  - `store.Restore.spec`: `⌜∃ d, γ.kb = some d ∧ d.cm = false⌝ ∗ ⌜d'.cm = false⌝` (Q5-3, Q5-4).
  - `NewStore.specW`'s pre: `kbWTSupplyM kb cm`, without `□`.
- **Exported results.** As listed, and `server_kv_*` gain `(hcm : d.cm = false)` (N4).
- **Trusted.** Unchanged: `storage.OpenBackend` by Q5-2 only.
- **D22's (the collaborator's).**
  - Statement text: `store.Restore.spec`'s two premises (Q5-3, Q5-4); `InvApplier`'s three
    `∃ d, E.γ.kb = some d` facts gain `∧ d.cm = false`.
  - Definitions and proofs, no statement text:
    - `KBReal.cm`, with `cm := false` in `SnapApplyWalk` and `SnapApplyDefs`;
    - `PhysNames.mk`/`StoreNames.mk`, `withPhys`/`phys` and the two `Countable` instances;
    - `store.Restore`'s literal `p'`;
    - `poolBody`'s sum (`poolSumW`, N5);
    - `RestoreMoves`' `writerRes (γ.withPhys p')`, which gains `mwSlotW` (`True`).
- **The server.** Only D22's literals, `InvApplier`'s facts, and the premise on `server_kv_*`.
  `NewServer.spec` stays unchanged (M2).

**Estimate:** about 1250–1600 lines, per round 15: the swap law is now proved in the Draft (+0 at the
switch), N3 +30, N2 (a) +50, N5 +30. One full build per round (1724 modules).

### Review round 16: question 5's Draft converged (2026-10-29)

Round 16 (`notes/spec-first-study/backend-review-16.md`, on `0ed5b49b3f`), the increment's third
round, has no first-tier finding, so the switch follows. The user confirmed Q5-4 (a) at its real
cost (2026-10-29): the `cm = false` premise travels down D22's snapshot path as round 16's M1 lists.
- `watchableStore.Restore.spec` takes both premises.
- `applySnapshot.specSnap` and its two walk lemmas take an `hcm` beside `hkb`.
- The snapshot's post carries `d'.cm = false`.
- At boot, `NewServer`'s proof uses `{ d with cm := false }`.
- Of `InvApplier`'s facts, only `srvEnvOk` takes the conjunct.

### Question 5's switch: stage 1, and the stages left (2026-10-29)

**Stage 1, done.** `KBReal` gains `cm : Bool` (Q5-1), with its `Countable` instance; D22's two
record literals in `SnapApplyDefs` set `cm := false`. `SnapApplyWalk`'s `{ d with … }` copies it.
`kbCmp` is not switched yet (still `kb = none`), so no statement means anything new.

**Why the switch is staged** (decided by the agent). Every compaction proof (`updateCompactRev`,
`scheduleCompaction` and its job, `checkPrevCompactionCompleted`, `compactLockfree`, `Compact`)
reaches the backend through `isKeyBackendG_cmp`, which reduces to mvcc's assumed backend
(`kb = none`: no tokens). Switching `kbCmp (some d) := d.cm` re-proves all of them over the real
backend's tokens: the job's reader and slot, the write-back supply, the key swap, and the
registration. That is the bulk of the 1300-1650 lines. The two switch laws
(`isKeyBackendG_congrDel`, `isKeyBackendG_weaken`) need the `Del`-monotonicity of `keyReadSnap` and
`isBatchTxG`, which is R4-4's pending lemma. So the laws are a stage of their own too.

**Stages left, in order, each built and committed:**
1. **Q5-2:** `newPost`/`newPostK` gain `srSlot b`, proved in `New` from the zero
   `safeRangeDeleteMu`. Repair the positional `newPost` patterns its importers use
   (`etc/importers.py --uses newPost InvNew.lean`).
2. **R4-4:** `Del`-monotonicity of `keyReadSnap`/`keyReadLocked` and `isBatchTxG`/`batchTxSpecG`.
   Then prove `isKeyBackendG_congrDel` and `isKeyBackendG_weaken` (F7), and make the old bridge an
   instance of the new. The old bridge's exports gain `fkV`, `hHK`, `hFV` and the three callee specs;
   `server_kv_*` get `fkV` from `newPost`'s `fkCl`.
3. **(iii):** `viewFk γb f` (opaque), `viewNoCmp := viewFk γb 0`, `kbMW` over the bucket's name.
4. **The core:**
   - `kbCmp (some d) := d.cm`, and a general compaction contract in place of `isKeyBackendG_cmp`;
   - `mwSlotW` in `writerRes`, `physCmpW` in `physOk`, `PhysNames.mk`, `mwSwap_of_inv` and
     `mwSwap_of_physOk`;
   - `store.restore` gives the half back;
   - `NewStore`/`New`/`newWatchableStore`;
   - `store.Compact` lending `storeRT`;
   - `Set*Compact` over `batchTxSpecG` with `mwSwapW`;
   - `compactTok` with `compactJobResM`;
   - re-prove the compaction proofs over the real backend.
5. **D22's side (Q5-3/Q5-4, M1):**
   - `store.Restore`/`watchableStore.Restore`'s premises;
   - `applySnapshot.specSnap` and its two walk lemmas' `hcm`, and the snapshot's post `d'.cm = false`;
   - `srvEnvOk`'s conjunct, and `NewServer`'s `{ d with cm := false }`;
   - `restore_switch`/`restore_finish`'s facts and `poolBody`'s sum (`restore_noCmp`);
   - `server_kv_*` `hcm`.
6. **Close:** `mvcc_NewStore_backend` at `cm := true` (the exported compaction results over a
   compacting real backend), delete `WiringDraft.lean`, and run the axiom skill on `OpenBackend`
   (Q5-2).

**Stage Q5-2, done (2026-10-29).** `newPost`/`newPostK` end with `srSlot b`, one reader's slot of
`safeRangeDeleteMu`. `newBackend`'s proof makes it from the field's zero value
(`sync.init_RWMutex` at the predicate `True`, one of the slots), and `backend_init` passes it into
`newPostK`. `bootBackend_of_newPost` drops it: the server stays `cm := false`. `storage.OpenBackend`'s
text is unchanged and its post means more, so the axiom check before Freeze stays listed.

**Stage R4-4 and the switch laws, done (2026-10-29).** New module `mvcc/ContractLaws.lean`, all
proved:
- **Monotone in the deletable keys:** `snapThin_mono`, `keyReadSnap_monoDel`,
  `batchTxSpecG_weaken`, `isBatchTxG_weaken`, `isKeyBackendG_weaken` (F7: at any `Cmp'` that does
  not hold, any `SR'`/`SRh'`/`MW'`), and `isKeyBackendG_weaken_noDel` (no deletable key).
- **Up to `◇`:** `except0_pure_wand`, `snapThin_congr`, `keyReadSnap_congrDel`,
  `batchTxSpecG_congrDel`, `isBatchTxG_congrDel`, `isKeyBackendG_congrDel` (the Draft's `.stmt`,
  with `□ (∀ k, Del k ∗-∗ ◇ Del' k)`). Covariant positions eliminate the `◇` through `wp_fupd`;
  the contravariant one (the job's delete) uses `Del' k ⊢ ◇ Del' k ⊢ Del k`.

**The old bridge is the new one's instance** (decided by the agent). `isKeyBackendG_of_backendC` now
takes the compaction condition `Cmp` as a parameter. Its compaction-only premises are guarded by
it: the three callee specs (`hLSR`, `hUSR`, `hUP : Cmp → …`), `hHK`/`hFV : Cmp → …`, and
`□ (⌜Cmp⌝ -∗ fkV γ true)`. `isKeyBackendG_of_backend` is that bridge at `Cmp := False`, weakened by
`isKeyBackendG_weaken_noDel` under `dlNoDel`. Its old proof is gone; the new bridge shares its
clauses. So the last variant is gone, and the old bridge's statement, with its callers
(`storeBackendT_of_backend`, `storeBackend_of_backend`, `mvcc_backend_bridge`,
`mvcc_storeBackend_of_backend`, `StoreBackend`, `BuildLemmas`, D22's walk), is unchanged. That is
fewer changes than the Draft predicted: the Draft's "the old bridge's exports gain `fkV`, `hHK`,
`hFV` and three callee specs" is not needed. The other option, the old bridge as the `Cmp := True`
bridge weakened, would have pushed those premises into D22's walk and `NewServer`'s link list.

**Stage (iii), partly done (2026-10-29).** `viewFk γb f` is the assumed backend's opaque flag, and
`viewNoCmp γb := viewFk γb 0` (until now opaque itself). No statement's text changes.

Moved into the core stage (decided by the agent): `kbMW` over the bucket's name, with
`kbMW none γb := ∃ f, viewFk γb f`. Switching the assumed backend's right from `True` breaks the
proofs that produce it trivially today: the job's `Meta` put in `store__scheduleCompaction`
(`unfold mvcc.kbMW; itrivial`) and `SetScheduledCompact`/`SetFinishedCompact`. They can take it only
from the store, once the right has its home (`mwSlotW`/`physCmpW`/`mwSwapW`, the core stage). The
signature change alone would be churn with no use. `WiringDraft`'s `viewFkW`/`kbMWW` stay as the
Draft's statements until then.

**Core stage, part 1: the read token (decision (i)), done (2026-10-29).** `checkPrevCompactionCompleted`,
`compactLockfree` and `store.Compact` take the store's reader token `storeRT γ` and give it back in
every case (`store.Compact`'s from the apply thread's `writerOwn`; no server caller yet: M2's). The
`ReadTx` clause's `RLock` takes it and `RUnlock` returns it (`metaReadTx rt RT`). New law
`isKeyBackendG_cmpRT` (`InvCompact.lean`): the contract over mvcc's assumed backend with the reader's
token left as `storeRT γ`, so `checkPrevCompactionCompleted`'s proof no longer depends on it being
`True`. Exported: `mvcc_store_Compact`'s text is unchanged (it is `store.Compact.spec`); its meaning
gains the token.

**Core stage: what remains, and why it is one piece** (decided by the agent, 2026-10-29). The rest
cannot be split into parts that each build and mean something:
- **The job's tokens.** `store__scheduleCompaction`'s job (765 lines) and `updateCompactRev` (341)
  reach the backend through `isKeyBackendG_cmp`, which turns every token into `True`. Over a real
  backend the job needs:
  - its reader token, for each batch's lock;
  - the safe-range slot, for `LockForSafeRangeDelete`;
  - a write-back token per `Unlock` and per `ForceCommit`, from the supply and its receipts;
  - the write right, for the `Meta` put of `finishedCompactRev`, through `mwSwapW`.
  `updateCompactRev`'s `SetScheduledCompact` session needs the write-back tokens and the write right
  too.
- **The resources must exist first:**
  - the job's budgets in `compactTok` (`compactJobResM`, `nJobRd` out of `poolBody`);
  - the write right's home (`mwKeyW`/`mwSlotW` in `writerRes`; `mwInvW`/`physCmpW` in `physOk`;
    `PhysNames`/`StoreNames.mk`), and `store.restore` handing back the half;
  - the write-back supply in `physOk`;
  - `NewStore`, `New` and `newWatchableStore` taking them.
- **The flip comes last.** Only then can `kbCmp (some d) := d.cm` replace `kb = none`, with a general
  contract lemma in place of `isKeyBackendG_cmp`, and the `cm = true` store's contract from
  `isKeyBackendG_of_backendC` at `Cmp := True` and `isKeyBackendG_congrDel` (`delKey` → `bkDel`).
- **Order for the next round:**
  1. The resources' definitions and `NewStore`'s statement, with the store's proofs carrying them.
  2. `updateCompactRev` and `Set*Compact` over a general contract.
  3. The job.
  4. The flip and the `cm = true` store.
  5. D22's side (stage 5).

### Review round 17 (stages 2-4) and its repair (2026-10-29)

Round 17 (`notes/spec-first-study/backend-review-17.md`) on stages Q5-2, R4-4 and (iii). Its one
first-tier finding is repaired, as decided by the agent:
- **The finding.** `isKeyBackendG_congrDel`'s premise `□ (∀ k, Del k ∗-∗ ◇ Del' k)` cannot be met
  from the bridge's `bkDel γB` to the store's `delKey γ`. Its backward direction,
  `◇ delKey ⊢ bkDel`, is unprovable: `dlIs` is persistent and has no `◇` to absorb.
- **The repair.** The premise becomes `□ (∀ k, Del k -∗ ◇ Del' k) ∗ □ (⌜Cmp⌝ -∗ ∀ k, Del' k -∗ Del k)`,
  and the same for `batchTxSpecG_congrDel` and `isBatchTxG_congrDel`. It is strictly stronger: only
  the compaction's delete uses the backward direction, under `Cmp`. `WiringDraft`'s `.stmt` follows.
- **Verified by the glue.** `storeDlReg_congr` (in `WiringDraft`, proved) gives both premises from
  `storeDlReg γB γ.idx`:
  - forward: saved-predicate agreement under `▷`, with `delKey` timeless;
  - backward: `dlIs` built from the registration itself.

  This is the third round on this statement, so there is no new review round for it.
- **Docs.** D1: `_of_backendC`'s docstring now says `Cmp` is a parameter; `kbCmp`'s and
  `InvCompact`'s comments are updated. D2: `kbMW`'s docstring now treats `viewFk` as existing.
- **M1, a note for later:** a future `Defrag` proof needs `safeRangeDeleteMu`'s guard
  (`isRWMutexGuard`) in `isBackend`, or a slot. `newBackend` keeps only one reader's slot today.

**Core stage, part (1a): the resources' definitions in their home (2026-10-29).** Moved from
`WiringDraft` into `InvStore.lean`, with the mode read from the field `KBReal.cm` instead of the
Draft's parameter `cm : KBReal → Bool`:
- `kbCmpM kb` (`none ↦ True`, `some d ↦ d.cm = true`) with its `Decidable` instance;
- `compactJobResM`, `kbWTSupplyM`, `kbSRM`, `nJobRd`;
- the laws `cmOff_res` (a real backend with `cm = false`: no reader kept back, every budget `True`)
  and `kbSRM_of_kbSR`;
- `delKeyI`, `delKey_eq_delKeyI`, `delKeyI_timeless` and `storeDlReg`.

`WiringDraft` drops its copies and the `cm` parameter; its other statements, glue and proofs are
unchanged. Nothing uses the new definitions yet, so no statement means anything new and `kbCmp` is
still `kb = none`.

**Part (1b), a finding for the next step** (decided by the agent; supersedes N5's `poolSumW`). The job's
reader can leave the readers' pool through the pool's existing retired count, not through a new sum.
`poolBody` already has `k + j + w + r = nReaders` with `r` the retired readers, and `NewStore` hands
out `retiredAt γ 0`. In compaction mode `NewStore` instead:
- starts the pool at `r = nJobRd kb`;
- gives `retiredAt γ (nJobRd kb)`;
- hands out `nReaders - nJobRd kb` readers.

So D22's `poolBody` and `restore_switch` don't change. Only the text of `NewStore`/`New`/
`newWatchableStore`'s posts and `BuildLemmas`' `retiredAt γw.st 0` do. With `d.cm = false` that text
is today's, via `cmOff_res`.

What part (1) still needs:
- **Tokens:** `compactTok` carrying `compactJobResM γ.kb`, and `NewStore` taking `kbSRM kb` (from
  `newPost`'s `srSlot`: `bootBackend_of_newPost` must keep it instead of dropping it).
- **The write right's home:** `mwKeyW`/`mwSlotW`/`mwInvW`/`physCmpW`/`PhysNames.mk`, which need
  `kbMW` over the bucket's name, the switch moved here from stage (iii).
- **`store.restore`** handing back the half.
- **`NewServer` at `{ d with cm := false }`** (M1). Its `d` is quantified in `bootOk`, so this is
  where stage 5's D22 changes become necessary.
