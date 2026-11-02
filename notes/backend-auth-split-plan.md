# The backend's specs for the auth split (spec-first: Scope, Draft, Impact, Review)

Branch `backend-auth-split` (2026-11-01). What the restated auth-on snapshot install's premise
(`snap-auth-on-draft`, `notes/snapshot-auth-on-plan.md`) needs of the storage backend, after the
user's decisions of 2026-11-01 on that Draft's questions. Draft module:
`Proof/go_etcd_io/etcd/server/v3/storage/backend/AuthSplitDraft.lean` (imported by nothing; the
laws of the new opaque predicates `sorry`, the glue and the corollaries proved). Status: decision 1
frozen and applied; decision 3 stopped (its law `rtHeldF_rbOwnIn` not provable over the backend's
read model); decision 2 held with the trusted restatements ("Freeze", the end of this note).

## Scope

The user's decisions, as this stage takes them:

1. **Release vs Close.** A read in progress (a held `readTx`, a `ConcurrentReadTx`) needs no
   `bOpen` share of its own; the guard is where Go's is, at the acquisition (`RLock`,
   `ConcurrentReadTx`); `Close` waits for the readers, as Go's does. Go (fork pin `7cf3644ec`):
   `backend.Close` (`backend.go:481`) closes `stopc` and waits for `run` (`<-b.donec`), whose stop
   branch calls `batchTxBuffered.CommitAndStop` (`batch_tx.go:368`) → `commit(true)`, which takes
   `readTx.Lock()` (`batch_tx.go:376`): it waits for every `readTx.RLock` holder. Then `db.Close()`
   waits for bbolt's read transactions (`ConcurrentReadTx`'s). After `Close` an `RLock` succeeds
   and `UnsafeRange` dereferences the nil bolt transaction (`axiomcx/close_test.go`).
2. **Readers backed by thread tokens** (the Bounds rule), not a partition of the backend's reader
   slots. Today: the constructor's post gives `List.replicate actualMaxReaders rdTok` (2^30 counted
   slots: a slot of `readTx.mu`, of `txMu`, a reader's budget token); mvcc keeps them in
   `bkRTx := rdTok ∗ bOpen rdOpen`, one per reader of the store, `bOpen 1` divided among them
   (`rdOpen`, `bOpen_one_shares`). `etc/bounds-check.py`: the backend package counts `stock` 12;
   `etc/bounds-allow.txt` lists none of it. Precedent: minibolt's `isDB` (`threadPool` of mmaplock
   slots, built by `Open` under `[ThreadBoundLe GF (2 ^ 30)]`, `dbReader_borrow`/`giveBack`) and
   rafthttp's `raftPool`/`raftLoan` (J8a-6).
3. **Per-bucket idleness.** `rbOwnIn` (the client's tracked buckets restricted to a set, idle:
   the readers see them), split/join laws, per-bucket `rbPut`. Today's `rbOwn γ r :=
   ghostVar γ.rbk ½ r` is **the writer's contents**, not what readers see: while a batch with a
   pending delete is held, readers still see the deleted key (`axiomcx/pending_test.go`). Go's
   `batchTxBuffered.Unlock` (`batch_tx.go:328`) writes the session's puts back into the read buffer
   under `readTx.Lock()` and commits when `pending >= batchLimit || pendingDeleteOperations > 0`
   (`:355`, etcd-io/etcd#17119): after `Unlock` the readers see the writer's contents on every
   tracked bucket (the pre-commit hook writes none: `hookStep`).

Also: trace who produces the mode-off auth contract (decision 6); report, no change.

What uses the predicates today (`etc/importers.py --uses NAME --count` on `InvBackend.lean`, of
2251 importers): `rbOwn` 14 modules, `rbPut` 10, `bOpen` 33, `rdTok` 12, `rtHeld` 8, `rtHeldF` 5,
`rdOpen` 5, `bOpen_one_shares` 2, `newPost` 14, `newPostK` 12, `isBackend` 76; `mvcc.bkRTx` 8
(`BackendBridge.lean`). Only one backend spec needs an open share during a read:
`readTx.UnsafeRange` (to rule out the stopped interval, `bOpen_stopped`); `ConcurrentReadTx`,
`RLock`, the batch locks take one at the acquisition and give it back; `concurrentReadTx.*` take
none.

## Draft

All in `AuthSplitDraft.lean`; a definition redefining an existing one carries its name under
`BksDraft.` (the merge drops the prefix).

### Decision 1: the held read records that it is live

```lean
def BksDraft.backend.rtHeldF γ P b rtx rv p : IProp GF :=
  iprop(rtHeldF γ P b rtx rv p ∗ ⌜rtx ≠ Loc.null⌝)      -- today's, and the transaction not nil
abbrev BksDraft.backend.rtHeld γ P b rtx rv := BksDraft.backend.rtHeldF γ P b rtx rv sync.rfrac.half

BksDraft.backend.readTx.RLock.spec:        -- today's statement over the new rtHeld
  {{ isPkgInit ∗ isBackend γ P W Pk b ∗ bF "readTx" b ↦□ rt ∗ rdTok γ P b ∗ bOpen γ qo }}
    rt.RLock()
  {{ RET #(); ∃ rtx rv, BksDraft.backend.rtHeld γ P b rtx rv ∗ bOpen γ qo }}
BksDraft.backend.readTx.UnsafeRange.spec:  -- today's, without `bOpen γ qo` in pre and post
```

A stopped interval's transaction is nil (`rtIntv`), so `rtx ≠ null` is liveness, stated without
`rd.live` (an internal field); today's laws carry over by framing the fact (round 1's T1). Proved:
`rtHeldF_old` (new ⊢ today's), `rtHeldF_of_open` (today's ∗ `bOpen` ⊢ new ∗ `bOpen`, by
`rtHeldF_lend` and `txLive_nonnull`: what `RLock`'s proof adds), the share-free laws a reader
without an open share needs, `BksDraft.rtHeldF_lend` (new `(p1+p2)` ⊢ new `p1` ∗ `txLive rtx p2`),
`BksDraft.rtHeldF_return`, `BksDraft.rtHeldF_read` (a returned slice read, no `bOpen`), and the
corollaries `BksDraft.readTx.RLock.spec_old` and `BksDraft.readTx.UnsafeRange.spec_old` (today's
statements follow: every caller unchanged). Liveness is stable while held: only the stop's commit
(`rtRes_cm_close`, under `readTx.Lock()`, the whole `γ.rd`) ends the interval.

`backend.Close.spec` is unchanged (`bOpen γ 1`): with no reader holding a share, the clients'
whole token is all it needs (its proof: unchanged, 59 lines; it never needed the readers' shares,
only `stop_take`'s). Its docstring gains: reads begun before it finish first (commit's
`readTx.Lock()`, bbolt's `Close`).

Glue for the auth realization's release (`authBkLife`'s `□ (authRetired ∗ authCur 1 ==∗ K ∗ …)`,
`K = bOpen authOpenQ`): `BksDraft.guarded_RLock` (proved; a frame of `RLock`): for any guard `G`
with `G q ⊢ |={⊤}=> bOpen γ (f q) ∗ (bOpen γ (f q) ={⊤}=∗ G q)` (the currency `Cu q`, the open
share in the realization's invariant; round 2: with updates),
`{{ … ∗ rdTok ∗ G q }} RLock {{ ∃ rtx rv, rtHeld ∗ G q }}`: the guard comes back at `RLock`, so the
whole `G 1` (hence `bOpen (f 1)`, for `Close`) can be released while reads begun before still run
`UnsafeRange` (no share needed). Over today's specs this is not realizable (a read holds
`bOpen qo` until `RUnlock`).

### Decision 2: a pool of reader slots

```lean
def BksDraft.backend.rdPool γ P b := ∃ γp, threadPool.isThreadPool rdPoolN γp (rdTok γ P b)  -- persistent
def BksDraft.backend.rdLoan γ P b := ∃ γp, isThreadPool rdPoolN γp (rdTok γ P b) ∗ ownThreadLoan γp
rdPool_init  : threadBound GF ≤ n + 1 → [∗list] replicate n, rdTok ⊢ |={E}=> rdPool
rdTok_borrow : rdPool ∗ threadTok ⊢ |={E}=> ▷ rdTok ∗ rdLoan
rdTok_giveBack : rdLoan ∗ rdTok ⊢ |={E}=> threadTok
```

All proved (over Perennial's `threadPool`). Glue, proved: `BksDraft.reader_RLock`
(`{{ … ∗ rdPool ∗ threadTok ∗ £1 ∗ bOpen qo }} RLock {{ ∃ rtx rv, rtHeld ∗ rdLoan ∗ bOpen qo }}`)
and `BksDraft.reader_RUnlock` (`{{ … ∗ rtHeld ∗ rdLoan }} RUnlock {{ threadTok }}`), over the
draft `RLock` and today's `RUnlock`.

Where the pool is built (Q2, open). Drafted: the constructor builds it, `BksDraft.backend.newPostK`
with `rdPool ∗ rdStock` in place of the replicated `rdTok`s, `rdStock` the counted remainder
(`rdStockN := actualMaxReaders - 2^28`), and `BksDraft.backend.New.spec` under
`∀ [ThreadBoundLe GF (2 ^ 28)]`, the bound J8a already gives the server's results (no weakening).
The pool is for the readers that hold no lock of their owner's across a read transaction, all on
the apply thread (`MustReadMembersFromBackend`, `schema/membership.go:95`; the alarm store's
`GetAllAlarms`, `schema/alarm.go:85`; `authStore.Recover`, `auth/store.go:403`; the auth admin
reads `UserGet`/`UserList`/`RoleGet`/`Authenticate` through `as.be`; round 4: `RoleList` and
`lessor.Recover` read under the batch lock, and `monitorStorageVersion` holds `bemu`, a counted
slot in `notes/bounds-locks.md`), which today borrow mvcc's `bkRTx` (five
trust-boundary specs take it: a counted partition in mvcc's vocabulary). The remainder is for the
owners whose readers nest a slot under their own read lock at acquisition (auth's `lockedReadTx`
takes `beMu.RLock()` around `tx.RLock()`; mvcc's reads under `s.mu`), which pool bundles that
contain a slot (`notes/bounds-locks.md`, B2): their slots move to them, counted, at their
constructors. (Round 2 dropped the pool on the premise that every reader holds an owner lock;
round 3 showed the premise false and the pool restored.)

### Decision 3: the writer's part and the idle part, per bucket set

```lean
opaque BksDraft.backend.rbPart γ (S : GoString → Prop) r : IProp GF
  -- the writer's contents hold r at the tracked buckets of S; only the holder writes them;
  -- a write of its own session may be pending (what rbOwn is today, for any S)
opaque BksDraft.backend.rbOwnIn γ S r : IProp GF
  -- rbPart, and no write to a bucket of S pending: the readers see r there too
def BksDraft.backend.rbOwn γ r := rbPart γ (fun _ => True) r       -- text and meaning kept
def BksDraft.backend.rbPut γ P n S := if P.RB n then rbPart γ (· = n) (rbData P S) else True
```

Laws (statements, `sorry`: the backend change's obligations): `rbPart_split`/`rbOwnIn_split`
(disjoint sets: the part of the union is the two parts), `rbPart_congr`/`rbOwnIn_congr` (a part
says nothing outside its set), `rbOwnIn_part` (idle ⊢ part), `rbPart_none`/`rbOwnIn_none` (the
empty set: `⊢`), timeless, `batchLocked_rbPart` (agreement with `rbData P st.S` on all of `S`: an
untracked name of `S` is absent from `r`),
`rtHeldF_rbOwnIn` (a held read agrees with the idle part: `∀ n k, S n → P.RB n → vOf P rv n k =
((r.lookup n).getD ∅).lookup k`). Proved over them: `rbOwnIn_set`/`rbPart_set`,
**`rbOwnIn_split_compl`** (the draft premise's `backend.rbOwn_split_in`, restated:
`rbOwnIn γ ⊤ r ⊣⊢ rbOwnIn γ S r ∗ rbOwnIn γ (¬S) r`; the draft's own statement, over `rbOwn`, is
false while a write is pending), `rbOwn_split`, `premise_buckets` (`rbOwnIn ⊤ r ⊢ rbOwnIn
authBkts r ∗ rbOwnIn restNonAuth r`), `rbPutAll_split`, `rbOwnIn_agree`, `batchLocked_rbOwn`
(today's exact `r = rbData P st.S`, round 2). Also stated: the lock's side `rbLock γ r`
(opaque) with `rbLock_agree` (agreement with any part on its buckets), for `backend.Snapshot`'s
observation (round 2: today's hands the lock's half as `rbOwn γ r`). (`rbPart_excl`, added in
round 2, dropped in round 4: no client, and unprovable over the writer's halves without a share
above ½ per bucket and a link from `γ.rbk`'s domain to `P.RB` in `isBackend`.)

Restated statements (each today's, but):
- `batchTxBuffered.UnsafePut.spec`, `UnsafeDelete.spec`: `rbPut` per bucket (the part of the
  bucket written only). Today's forms corollaries (`UnsafePut.spec_all`, `UnsafeDelete.spec_all`,
  proved; `rbPutAll`).
  `UnsafeCreateBucket`/`UnsafeDeleteBucket`: the same change, not drafted.
- `batchTxBuffered.Unlock.spec`: extra binders `(S : GoString → Prop) (r)`, `rbPart γ S r` in the
  pre, `Q ∗ rbOwnIn γ S r` in the post (a part handed in comes back idle). Today's a corollary
  (`Unlock.spec_old`, `S := ⊥`, proved).
- `newPostK`: `rbOwnIn γ ⊤ (rbData P D)` in place of `rbOwn γ (rbData P D)` (a fresh backend is
  idle); the reader slots as today.

The representation (the Prove phase's): `γ.rbk` a ghost map over the tracked names (the writer's
halves) and a second over the readers' contents. Per bucket, `rbPart` holds the readers' client
half **or** a receipt for it deposited in the batch lock (round 3: so that `rbOwnIn_part`, an
entailment, can forget idleness without an update, and `Unlock` can redeem the receipt); `rbOwnIn`
holds the half itself. A session's first write to a bucket deposits the half, if the part has it. The tracked names must be finite (`⊆ P.BT`'s): perhaps a `P.Wf` conjunct.

## Impact (not applied)

With the corollaries, no caller of `RLock`, `UnsafeRange`, `UnsafePut`, `UnsafeDelete` or `Unlock`
must change; what does:

| what | users (modules) | change |
| --- | --- | --- |
| `readTx.UnsafeRange`, `RLock` restated | backend's own proofs (`readTx__RLock`, `readTx__UnsafeRange`) | `RLock`: `rtHeldF_of_open` before returning; `UnsafeRange`: the `live = false` branch goes (`rtHeldF`'s fact) |
| callers of `UnsafeRange.spec` | 9 (applySnapshot, NewServer, SnapApplyWalk, BuildLemmas, StoreBackend, M2StorageDraft{,Restore}, BackendRecs, BackendBridge) | none (corollary); optionally drop the `bOpen` they thread |
| `rtHeld`'s body (redefined) | `rtHeld_wf` (`BackendBridge.lean:633-641`, unfolds `rtHeld rtResAt rtRest rtCore` positionally) | moves to the backend as a law (it breaks at the merge otherwise) |
| `backend.Snapshot` (trusted axiom) | its spec, `SnapSendBranch` (`:216-230`, unfolds `rbOwn` and combines its half with the lock's) | the observation wand hands `rbLock γ r` in place of `rbOwn γ r`; `SnapSendBranch` uses `rbLock_agree`. In mode on the server holds only `rbOwnIn restNonAuth`, so `snapObs_window`'s `r = rb` covers only those buckets: the auth buckets of a sent snapshot (the receiver's `authBucketsAt`) need an observation clause from the auth premise (gap, for the #7-on sender) |
| `mvcc.bkRTx := rdTok ∗ bOpen rdOpen`, `rdOpen`, `bOpen_one_shares` | `bkRTx` 8, `rdOpen` 5, `bOpen_one_shares` 2 | Q5. Keeping `bOpen rdOpen` in `bkRTx` makes a read in flight hold a share of the old backend, so the closer's `bOpen 1` cannot be reassembled and the auth premise's release is not realizable (round 2). Dropping it leaves mvcc's readers no source for the share `RLock`/`ConcurrentReadTx` take at acquisition (round 3). So it is replaced, not dropped: an acquisition guard in mvcc's store, a currency in the store's invariant (with the store's open share inside) lent under `s.mu`'s read side and returned at `RLock` (`guarded_RLock`'s `G`), the closer collecting the whole currency; `bkRTx := rdTok`, `rdOpen`/`bOpen_one_shares` go, and the restore's count (`k + j + w + r = nReaders`, `RestoreMoves.lean`) loses its open-share part. Not drafted |
| `rbOwn` (now `rbPart ⊤`) | 14 importing modules; 31 files mention it (13 outside the backend and mvcc are specs) | none by text. The specs taking the whole `rbOwn`: 10 trust-boundary axioms (membership `RaftCluster.Recover`/`SetBackend`, schema `MustSave`/`MustDelete`/`MustReadMembersFromBackend`, v3alarm `NewAlarmStore`/`AlarmStore.restore`, lease `NewLessor`/`lessor.Recover`, auth `NewAuthStore`) and 2 proved (`EtcdServer.restoreAlarms`, `AlarmStore.Recover`, which pass it through): restated over their own buckets (Q4), so that the mode-on server can hold only `rbOwnIn restNonAuth`. Those that **read** the buckets through `be.ReadTx()` (`MustReadMembersFromBackend`, and `RaftCluster.Recover` through it) take the **idle** part `rbOwnIn` of theirs, and give it back; those that lock the batch themselves and `Unlock` (`NewLessor`, `AlarmStore.restore`, `NewAuthStore`, the member writers `MustSave`/`MustDeleteMemberFromBackend`) take `rbPart` and give back `rbOwnIn` (so the member reads after them can be called). The carriers of the whole `rbOwn` shrink with them (and carry `rbOwnIn` where a member read follows): `srvRestOwn`/`srvRestRW` (`InvRest.lean:331,336`), the auth write right `∃ r, rbOwn` (`apply/Contracts.lean:208`), `applyConfChange`'s frames (`EtcdServer__applyConfChange.lean:246-268,470-501`), mvcc's `kbRb`/`storeRb` (`InvStore.lean:1941-1943`, `BackendBridge.lean:3090,3272`), the lessor's `Rb` (`NewServer.lean:1293`, `SnapRO.lean:127`, `SnapApplyOptsLemmas.lean:191`). A part written through mvcc's bridge with `Unlock`'s `S := ⊥` (the lessor's `Revoke` delete) comes back not idle: the server's mode-on carrier is `rbPart` of the lessor's bucket and `rbOwnIn` of `members`, or the bridge passes the part to `Unlock` |
| `rbPut` per bucket | 10 (InvBatch, `UnsafePut`/`UnsafeCreateBucket`/`UnsafeDelete`/`UnsafeDeleteBucket` specs and proofs, BackendBridge, CindexBackend, `OnPreCommitUnsafe`, `NewLessor` spec) | the 4 specs' proofs over the part; `NewLessor`'s (trusted) its bucket's part; the proved callers on untracked buckets (`rbPut_other`) unchanged, but `BackendBridge.lean:2050-2055` unfolds `rbPut` on the tracked `lease` bucket to `rbOwn` (the lessor's delete): it goes through `UnsafeDelete.spec_all`/`rbPutAll_split` instead |
| `Unlock.spec` restated | 8 direct users + backend internals | none by text (corollary, `S := ⊥`); but a caller passing `⊥` gets no idle part back, so every server site whose part later reaches a reading axiom (the member reads after the apply's batch: `applyConfChange`, the snapshot install's `RaftCluster.Recover`) passes its buckets as `S`, and the auth premise's realization `authBkts` |
| `newPost`/`newPostK` | 14 / 12 (`BootBackend`, `SnapApplyOpen`, `NewAlloc`, …) | `rbOwnIn ⊤` for `rbOwn` (`rbOwnIn_part` gives today's); the reader stock: `rdPool ∗ rdStock` for `replicate actualMaxReaders rdTok`. Every consumer of the full stock changes count: mvcc `New`/`NewStore`/`newWatchableStore` (`actualMaxReaders` copies of `kbRT`, `Spec/.../mvcc/New.lean:48`, `NewStore.lean:106`, `newWatchableStore.lean:52`), `store.Restore` (`nReaders`), `BootBackend.lean:56-91`, `RestoreMoves` (round 4) |
| `storage.OpenBackend` (trusted axiom, post `newPostK`), `OpenSnapshotBackend` | their specs (`Spec/.../storage/OpenBackend.lean:45-53`), `InvOpen`, `SnapApplyWalk`, `mvcc/Image`; callers boot and `applySnapshot` | take `[ThreadBoundLe GF (2 ^ 28)]` as `New` does: with the pool in `newPostK` and no bound the axiom would assert a pool of `2^28` slots under any thread bound, unsound (round 4) |
| `New.spec` under `ThreadBoundLe GF (2^28)` | `New`'s callers: `newBackend` → `openBackend`/`bootstrap` → `NewServer`, the snapshot install, the examples' adequacy | the instance threads to the closed results, which J8a already puts at `2^28` (no weakening) |

**A bug in today's specs (round 1's T3).** `MustReadMembersFromBackend.spec` (and
`RaftCluster.Recover.spec`, which reads through it) take `rbOwn` (the writer's contents) and
conclude that the read sees it; their docstring assumes "the caller holds no batch lock", which
neither precondition states. A caller inside a batch with a pending write to `members` reads the
old contents (`axiomcx/pending_test.go`, for a delete; a put is not written back before `Unlock`):
both axioms are false as stated today. The restatement over `rbOwnIn` repairs them (the idle part
cannot be held across a pending write of its buckets). Whether a proved caller reaches the false
case today is not checked here.

**A second bug of the same kind (round 4).** `authRecoverOk` (`SnapRO.lean:216-231`, in the
`NewAuthStore` axiom's post) takes `rbOwn dn.γB r` with the auth bucket at `authBoot` and concludes
the store stays disabled, but `Recover` reads through `ReadTx` (`auth/store.go:403-410`), which
does not see a held batch's pending writes: a batch deleting `authEnabled` and the users, held
across `Recover`, puts the writer's contents at `authBoot` while `Recover` enables the store
(`axiomcx/review4_test.go`, `TestR4RecoverInsidePendingBatch`). Restated: `authRecoverOk` takes
and returns `rbOwnIn dn.γB authBkts r`, with the member reads in the Impact's readers' list.

## The mode-off auth contract (decision 6): who produces it

The producers: the trusted `auth.NewAuthStore` spec (`Proof/go_etcd_io/etcd/server/v3/auth/
NewAuthStore.lean:26`, an axiom) gives the store, its reader bundles (`actualMaxReaders` copies
of `RD`) and `authRecoverOk` (`SnapRO.lean:216`), the mode-off `Recover` contract, consumed by the
snapshot install's `Recover`. A mode-off `authSchemaSrv` does not exist (today's `AuthSrv.lean`
one is mode on). In mode off the permission checks return early: no client's read reaches the
backend through them (`authReadTxOk` at `.off`). The backend is read inside `NewAuthStore` (the
boot thread, `bOpen qo` held), `Recover` (the apply thread; `bOpen qo` and `mvcc.bkRTx` lent per
call and returned), and the admin reads `UserGet`/`UserList`/`RoleGet` (and `RoleList`, under the
batch lock), in every mode
(`authStore__UserGet.lean`, `authInv st R M`, round 3), which run on the apply thread too, in
sequence with `Recover` and before the closer. Recommendation: no guard in mode off (the apply
thread's sequencing is the guard; not proved here); decision 2 replaces `authRecoverOk`'s `bkRTx`
loan and the admin reads' bundle with a loan from the backend's pool (`rdPool` ∗ the apply
thread's `threadTok`), when Q2 lands.

## The axiom check

The restated backend specs of this Draft are proved ones (bbolt's `DB.Close_kv` unchanged); but the
Impact restates trust-boundary axioms: `storage.OpenBackend` (its post `newPostK`, which gains the
pool and idleness, and the thread bound), `backend.Snapshot` (its observation over `rbLock`),
`NewAuthStore` (its `authRecoverOk`, false today), and the 10 specs taking `rbOwn` (Q4). Each of those is an axiom change for the user, with the collections
resting on it (`etc/tcb-report.py --roots`), and gets its own axiom check when drafted (not done
here). The restated semantics were checked against Go anyway (the scratch fork at the pin,
`axiomcx/split_test.go` next to `close_test.go`/`pending_test.go`): a delete then `Unlock`, the
readers no longer see the key (`TestUnlockIdleDelete`); a put below the batch limit then `Unlock`,
seen (`TestUnlockIdlePut`); pending puts and a pending delete on other tracked buckets (lease,
members) leave the auth bucket's contents visible (`TestOtherBucketsPending`); a `ConcurrentReadTx`
begun before `Close` reads, `Close` waiting for it (`TestConcurrentReadBegunBeforeClose`); a held
`readTx` reads repeatedly while `Close` is pending, which does not return before `RUnlock`
(`TestManyReadsWhileClosePending`). All pass; `RLock` after `Close` panics in `UnsafeRange`, as
the acquisition guard requires.

## Questions for the user

1. **Q1, `Close`.** Keep `Close.spec`'s statement (`bOpen γ 1`) and change only its docstring (reads
   begun before it finish first)? Recommended: yes; its proof is unchanged and the margin is Go's.
2. **Q2, the reader pool.** (a) the constructor builds a pool of `2^28` slots (J8a's bound) for the
   apply thread's lock-free readers and leaves the rest counted for mvcc's and auth's bundle pools
   (drafted); (b) no backend pool, each owner pools bundles with a counted slot, the lock-free
   readers taking a slot from a counted stock of their own; (c) Perennial-level reader tokens.
   Recommended: (a), the Bounds rule's shape where the slots are owned, at no thread-bound cost.
3. **Q3, `Unlock`.** A part handed in comes back idle through extra binders `S r` (drafted), with
   today's statement a corollary at `S := ⊥`? Recommended: yes.
4. **Q4, the trust-boundary specs taking `rbOwn`.** Restate the 10 over their own buckets: the
   readers (`MustReadMembersFromBackend`, `RaftCluster.Recover`, `authRecoverOk`) over the idle
   part, the self-locking writers over the part, giving the idle part back. Recommended: yes; it
   also repairs the three false today.
5. **Q5, mvcc's `bkRTx`.** Replace its open share by an acquisition guard in the store (a currency
   lent under `s.mu`'s read side, back at `RLock`), so that a read in flight holds no share of an
   old backend. Recommended: yes, as its own stage before the auth-on install's Prove.
6. **Q6, mode off.** No guard (the apply thread's sequencing); only the loans move to the pool.
   Recommended: yes.
7. **Q7, readers of a bucket whose writer's part is out.** The Draft states nothing of them; the
   auth readers' clause, today's and the auth Draft's, relies on what they see then. To be settled
   with the auth premise, not in the backend (details to the coordinator).

## Review rounds

### Round 1 (fresh `spec-reviewer`, given the Go code, the draft, today's specs and the callers)

No draft statement falsified by a Go execution (checked: `rtHeldF`'s liveness, `UnsafeRange`
without a share, `Close` with readers in flight, `Unlock`'s idle post, `rtHeldF_rbOwnIn`, the
split laws). First tier:

- **T1, no read law without the open share.** `rtHeld_read`, `rtHeldF_read`, `rtHeldF_lend`
  (`ReadLemmas.lean:1019,1058,1112`) and mvcc's `rtHeld_lendQ` take `bOpen`, and the draft's
  `rtHeldF` (with `rd.live = true` inside today's body) could not reach them without one.
  Repaired: `rtHeldF` is today's ∗ `⌜rtx ≠ Loc.null⌝` (the reviewer's proposal); share-free
  `lend`/`return`/`read` proved; `rtHeldF_of_open` reproved over `rtHeldF_lend`/`txLive_nonnull`.
- **T2, readers while a part is out.** The draft says nothing of what a reader sees of a bucket
  whose writer's part is out (from a session's first write to its `Unlock`'s return), and the
  auth readers' clause needs it. Not repaired in the backend: the question goes to the user (Q7).
- **T3, the reading axioms must take the idle part.** The Impact's "restated over their own
  buckets' part" would keep `MustReadMembersFromBackend`/`RaftCluster.Recover` false (above).
  Repaired in the Impact: the readers take `rbOwnIn`, the lockers `rbPart`; `Unlock`'s callers
  pass `S` where an idle part is needed later.

Second tier, repaired: `guarded_RLock`'s guard law one direction (`⊢`), docstring no longer
claims what `UnsafeRange` shows; `session_idle` renamed `rbOwnIn_agree`; `rbPart_excl` added.
Second tier, open: the tracked names finite (a `P.Wf` conjunct) and `rbPart`/`rbOwnIn` not
taking `P`; on the server's backend the auth buckets are hook buckets (`bridgeParams`), outside
the readers' view `vData`, so `rtHeldF_rbOwnIn` for them needs the readers' model extended (the
auth Draft's Q2 survey: 2.5–10k lines); `UnsafeCreateBucket`/`UnsafeDeleteBucket`/`newPost`
not restated; `ConcurrentReadTx` has no pool glue, and must get no idle law (its cache serves
stale reads after a commit: `issues/etcd-backend-read-buffer-cache-stale-after-commit.md`);
`rdStock` and `ThreadBoundLe (2^29)` are transitional counted stock.

### Round 2 (fresh `spec-reviewer`, the same material; the round-1 record read last)

No draft statement falsified by Go (traced by hand: `batch_tx.go:328-427`, `tx_buffer.go:96-115`,
`backend.go:481`); decision 1 judged ready. First tier:

- **No client for a backend pool** (above, Q2): every reader already holds its owner's read
  lock. Repaired: no pool in `New`'s post; the slots stay counted, the owners pool bundles.
- **`rbPart_excl` against `backend.Snapshot`'s axiom**: its observation hands the lock's half as
  `rbOwn γ r`; with exclusivity a caller holding its own part derives `False` in the wand, so the
  axiom would give any `⌜Q⌝`. Repaired: the lock's side `rbLock` with `rbLock_agree`; the Impact's
  new row (`Snapshot`, `SnapSendBranch`).
- **The Impact's missing rows**: `Snapshot`; the carriers of the whole `rbOwn`; what the
  self-locking writers give back; `BackendBridge`'s unfolding of `rbPut` on `lease`; Q5 likely
  required. Repaired in the table.

Second tier, repaired: `guarded_RLock`'s guard law with updates; `rbPart_excl` tied to `P` through
`isBackend`; the exact agreement `batchLocked_rbOwn` (agreement on all of `S`, untracked names
absent); `UnsafeDelete.spec_all` drafted. Open: `reader_RLock`'s `£ 1` (the borrow's `▷`), moot
while no client uses the backend-level glue.

### Round 3 (fresh `spec-reviewer`, the same material)

No statement false against Go (three more tests: a put into a bucket created in the session after
a reader cached it missing, seen after `Unlock`; a written-back put deleted in the next session,
gone; `UnsafeDeleteBucket` then `Unlock`, the bucket gone). Decision 1 judged ready. First tier:

- **F1, round 2's repair wrong**: many readers hold no owner lock (above). Repaired: the pool
  restored in the constructor at J8a's `2 ^ 28`, the remainder counted; Q2 left open.
- **F2, Q5 a deletion with no replacement.** Repaired in the Impact: an acquisition guard in
  mvcc's store (not drafted).

Second tier, repaired: the axiom-check section corrected (the Impact restates axioms);
`rtHeld_wf`'s row; the representation's per-bucket "half or receipt"; `batchLocked_rbOwnIn`
(observation without spending idleness); the decision-6 trace (the admin reads); `rbPut_other`
restated; the mode-on sender's auth-bucket gap in the `Snapshot` row. Open: `Close`'s docstring
change (in the plan, not drafted); the pool glue's `£ 1`.

### Round 4 (fresh `spec-reviewer`, the same material)

No statement false against Go (the nine split/close tests re-run; `batch_tx.go:328-427`,
`backend.go:463-486` traced); decision 1 judged ready. First tier, all in the Impact and the
axiom check, repaired there: **I1** round 3's pool repair not carried to the Impact (the stock's
consumers; `OpenBackend`'s post is `newPostK`, unsound without the thread bound); **I2** T3's
repair incomplete (`authRecoverOk` is a reading clause, false today, above); **A1** the axiom
check's list. Second tier: `rbPart_excl` dropped (D1); the pool's clients corrected (D2); the
carriers completed (I3); `RoleList` (M1). Open: `rdPoolN` one namespace for every backend (an
install holds two; harmless unless both pools are opened at once, a `γ`-derived name cleaner);
the read model's extension to hook buckets uncosted (the readers' state is already ghost-tracked,
so perhaps less than the auth Draft's estimate).

The rounds stop here: rounds 2-4 found no false statement in the Draft; their first-tier findings
were in the Impact (a client or a consumer missed, the same kind each round: T3, I2) or are the
user's questions (Q2, Q5, Q7).


## The user's decisions (2026-11-01)

All seven recommendations accepted: Q1 `Close.spec` unchanged (docstring only); Q2 (a), the pool in
the constructor at `2^28` with the counted remainder; Q3 `Unlock`'s extra `S r`; Q4 restate the 10
specs taking `rbOwn` (readers over the idle part, writers over the part); Q5 `bkRTx`'s open share
replaced by an acquisition guard in mvcc, its own stage; Q6 no guard in mode off; Q7 settled with
the auth premise (round 1's reviewer's Go finding is recorded outside this repository).

Next: Freeze of decisions 1–3 (the proved restatements, their corollaries, the callers), then the
trusted restatements (Q4's 10, `OpenBackend`/`OpenSnapshotBackend`, `Snapshot`), each drafted with
its axiom check and its text shown to the user before it changes.


## Freeze (2026-11-01)

**Applied: decision 1.** `rtHeld`/`rtHeldF` with `rtx ≠ Loc.null` (in their pure conjunct, the same
predicate as the draft's); `readTx.RLock`'s proof establishes it (`rtResAt_live`); `readTx.UnsafeRange.spec`
without the open share; the share-free laws `rtHeldF_lend'`/`rtHeldF_read'`, today's as corollaries;
`rtHeld_wf` a backend law (from `BackendBridge.lean`); `guarded_RLock` (`ClientLaws.lean`);
`Close.spec`'s docstring (Q1). Callers: `rtUR_held` and `rt_rangeLimF` frame the share, no other
change. The draft module keeps decisions 2 and 3, over the applied `rtHeldF` and `RLock`.

**Stopped: decision 3.** `rtHeldF_rbOwnIn` (a held read agrees with the idle part) is not provable
over the current representation: on the server every tracked bucket is a hook bucket
(`bridgeParams`), and the backend's invariants relate the readers' state to the writer's contents
only off the hook buckets (`sessWf`'s `agreeOff P.HB`, `vData`, `viewSame`, `hookStep`'s write
buffer clause): a reader's view of a tracked bucket is unconstrained. Proving it means extending the
read model to the tracked hook buckets (round 1's second-tier note; the auth Q2 survey's 2.5–10k
lines): `sessWf` and every batch operation's preservation, the write-back, the commit, the hook
window, `Unlock`. The other laws are provable over a per-bucket ghost map, but `Unlock`'s
restatement and the idle constructor need `rbOwnIn`, and `rbOwn`'s new representation changes
what `backend.Snapshot`'s axiom asserts. Nothing of decision 3 applied.

**Held: decision 2** (the pool in `newPostK` changes `storage.OpenBackend`'s axiom).

**The trusted restatements** (Q4's ten, the two pass-throughs, `Snapshot`, `OpenBackend`/
`OpenSnapshotBackend`): drafted with their axiom check outside the repository, for the user's
approval of their text; not applied.

**A defect of today's `MustReadMembersFromBackend.spec`, found by the axiom check** (this
repository's, not Go's): its pre has no premise that the `members` and `members_removed` buckets
decode, and Go panics on a key that is not a member id or a value that is not a member's JSON
(`schema/membership.go:91-122`, `lg.Panic`; the scratch fork's `axiomcx`
`TestBksReadUndecodableMember`: a put of key `zz` through the batch transaction, then the read
panics). Its restatement adds the premise (`membership.membersDecode`). Not checked: whether a
proved caller reaches it (the apply thread's members are `MustSaveMemberToBackend`'s encodings; a
Lean counterexample would write the key through the proved `UnsafePut`).

## The user's decisions on the Freeze's questions (2026-11-01)

All seven recommendations accepted:

1. **Decision 3, option (b).** `rbOwnIn` is a ghost idle token (a per-bucket pending flag the
   session's writes set and `Unlock` clears), not tied to the readers' model: the trusted readers
   that take it argue from Go, each axiom's docstring saying why. Option (a), extending the read model
   to the tracked hook buckets so that `rtHeldF_rbOwnIn` is proved, is a later stage (below).
2. **`MustReadMembersFromBackend`'s decoding premise** fixed in the trusted step, defined from
   `memberKey`/`memberEnc` (it excludes a `null` value).
3. **The trusted set grows** to `srvRestOwn`/`srvRestRW` and `bootOk` (its `clusterApplyOk` and
   `newPost`), with the self-locking writers taking any bucket set containing their own.
4. **The pool:** a core `OpenBackend` axiom with the pooled spec a proved corollary; the thread bound
   a persistent server fact built at `NewServer`, not an instance threaded through the specs between.
5. **The alarm, `storeRT` and `bkRTx` readers move onto the pool now** (drafted with the trusted
   step, applied with it).
6. **The `etc/bounds-allow.txt` entry for the draft** stays.
7. **Merge origin/lean** (for the `proof_roots`/`gen-link` fixes); check `memberEnc`'s round trip on
   attributes that are not valid UTF-8.

## Later stage: the read model over the tracked hook buckets (option (a))

What would make `rbOwnIn`'s meaning a theorem instead of the trusted readers' Go argument: the law
`rtHeldF_rbOwnIn` (a held read agrees with the idle part on its tracked buckets). Today the backend
relates the readers' state to the writer's contents only off the hook buckets (`sessWf`'s
`agreeOff P.HB`, `vData`, `viewSame`, `hookStep`), and on the server every tracked bucket is one
(`bridgeParams`). The stage extends the readers' model to the tracked hook buckets: `sessWf` and
every batch operation's preservation, the write-back, the commit, the hook window, `Unlock` (the auth
Q2 survey's estimate: 2.5–10k lines). With it, the trusted readers' axioms that take `rbOwnIn` could
become proofs over `readTx` (their bodies are `RLock`/`UnsafeRange`/`RUnlock` loops).

## State after the Freeze's step 1 (2026-11-02)

Applied (untrusted, no axiom or sorry added; TCB at its baseline): decision 1; decision 3's option (b)
(`rbPart`/`rbOwnIn`/`rbOwn` over a per-bucket ghost map with pending flags; the writers per bucket;
`Unlock` any part to idle; `Unlock.bare`); the seal (`rbSide` `@[no_expose]`, the flag-clearing and
raw update laws private). Drafted for the user (trusted, not applied): the revised restatements,
revision 3 with round 4's fix (scratch `bks-trusted.md`, four spec-reviewer rounds: round 2 the
forgeable flag, round 3 unpinned ghost names in the membership texts, round 4 `restore` over an
untracked bucket, each fixed in the draft; the last not re-reviewed). With the trusted step: the
`import all` gate on the backend's modules (part of the readers' trust base), the creators' table
premises, the pool's stock counts, `New`/`OpenBackend` giving `rbOwnIn`.

## The user's decisions on the Freeze's second questions (2026-11-02)

1. **Q1, `membersDecode`: the strong form**, with the invariant `memIdOk` (a member's id is its
   key) proved. Applied: `RestMemId.lean`, `restModel_memIdOk` (the applied log keeps it, from a
   boot that has it). The boot does not, as the model stands: `memBoot` keeps `ccMemberOf cc.context`,
   whose `id` is opaque; the trusted step proposes `memBoot` with `ccMemberAt` (Go's bootstrap
   members are keyed by their own id), a trusted-text change (`bks-trusted.md` §18).
2. **Q2**: `threadTok` threaded through the apply-thread specs (`applyAll`, `applySnapshot`,
   `applyConfChange`, `NewServer`).
3. **Q3**: the applied creators' dependence on `γ.rbD` accepted until the trusted step adds the
   table premises (`notes/decisions.md`).
4. **Q4**: the stock's consumers restated over `rdStockN`; the slot count left in specs between is
   a later Bounds cleanup (`notes/bounds-plan.md`).
5. **Q5**: `backend.Snapshot` unchanged.
6. **Q6**: `etc/api/backend.txt` and the `import all` gate land with the trusted step (drafted now).
7. **Q7**: §2–§10's docstrings written in full in the draft.

## Next stage (the user's decision of 2026-11-02, Q9): the cluster contract's rows

Right after this stage, on its own: the rows of `bootOk`'s `clusterApplyOk`
(`apply/Contracts.lean:525-549`) are false of Go at some rest states (`notes/decisions.md`,
"Defects of the applied cluster contract"): `UpdateAttributes` of an unknown id (a row premise: the
id in `r.mem` or removed, from the workload), `SetVersion` above the server's version (a premise on
the version), a missing `members`/`cluster` bucket (`srvRestOwn` holding them present,
`restModel_present`), and the attribute row's read-only `ClientURLs` slice (to check in Lean).

## Approval (2026-11-02)

The user approved revision 4.3 of the trusted restatements (§1–§19, with T), no further review
round; the apply step follows (the texts: the scratch draft `bks-trusted.md`, copied into the
repository as they are applied).

## Change log after the freeze

Every change to a statement frozen at "Freeze" (2026-11-01) or approved at "Approval" (2026-11-02),
one entry each, tagged when made (`notes/spec-first-plan.md`, "The change log after the freeze,
classified"): `[category, how found, public/trusted/internal, approval]`. The entries up to
2026-11-02 were classified after the fact by one reader, from this note and the commits
(`notes/spec-first-study/snapshot-proof-first.md`).

- `[R, proof, internal, the user's option (b)]` Decision 3: `rbOwnIn` as the idle part the readers
  agree with → a per-bucket ghost idle token, the trusted readers arguing from Go
  (`18956eff57`). The law `rtHeldF_rbOwnIn` is not provable over the backend's read model (no
  agreement on the hook buckets); found applying it, after four review rounds.
- `[D, user, trusted, approved]` Decision 2, the pool: a core `OpenBackend` axiom with the pooled
  spec a proved corollary; the thread bound a persistent server fact (the Freeze's Q4).
- `[E, user, trusted, approved]` The trusted set grows to `srvRestOwn`/`srvRestRW` and `bootOk`
  (Q3); the alarm, `storeRT` and `bkRTx` readers onto the pool now (Q5).
- `[D, user, internal, approved]` `threadTok` through the apply-thread specs; the stock's consumers
  over `rdStockN` (second questions, Q2, Q4).
- `[F, test, trusted, approved]` Outside the stage's statements: `MustReadMembersFromBackend` takes
  the buckets' decoding (`membersDecode`, the strong form with `memIdOk`), Go panicking on an
  undecodable member (the axiom check's `TestBksReadUndecodableMember`).
- `[F, Go, trusted, next stage]` Outside the stage's statements: the applied cluster contract's
  rows false of Go at some rest states (round 6; "Next stage").
- `[C, proof, trusted, as approved]` Applying revision 4.3: item E's boot fact spelled out as four
  conjuncts of `bootOk`'s `%Hbe` (the draft names it, does not spell it out). Otherwise applied as
  approved.

Review misses of the stage's own frozen statements so far: F 0, R 1.
