# The backend's specs for the auth split (spec-first: Scope, Draft, Impact, Review)

Branch `backend-auth-split` (2026-11-01). What the restated auth-on snapshot install's premise
(`snap-auth-on-draft`, `notes/snapshot-auth-on-plan.md`) needs of the storage backend, after the
user's decisions of 2026-11-01 on that Draft's questions. Draft module:
`Proof/go_etcd_io/etcd/server/v3/storage/backend/AuthSplitDraft.lean` (imported by nothing; the
laws of the new opaque predicates `sorry`, the glue and the corollaries proved). Status: Draft and
Impact done, review rounds below; stopped before Freeze.

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
  -- today's rtHeldF body, with ⌜rd.rtx = rtx ∧ rd.live = true⌝ in place of ⌜rd.rtx = rtx⌝
abbrev BksDraft.backend.rtHeld γ P b rtx rv := BksDraft.backend.rtHeldF γ P b rtx rv (1:Qp).half

BksDraft.backend.readTx.RLock.spec:        -- today's statement over the new rtHeld
  {{ isPkgInit ∗ isBackend γ P W Pk b ∗ bF "readTx" b ↦□ rt ∗ rdTok γ P b ∗ bOpen γ qo }}
    rt.RLock()
  {{ RET #(); ∃ rtx rv, BksDraft.backend.rtHeld γ P b rtx rv ∗ bOpen γ qo }}
BksDraft.backend.readTx.UnsafeRange.spec:  -- today's, without `bOpen γ qo` in pre and post
```

Proved: `rtHeldF_old` (new ⊢ today's), `rtResAt_live` (`rtResAt ∗ bOpen ⊢ … ∗ ⌜rd.live⌝`, by
`bOpen_stopped`), `rtHeldF_of_open` (today's ∗ `bOpen` ⊢ new ∗ `bOpen`: what `RLock`'s proof
adds), the corollaries `BksDraft.readTx.RLock.spec_old` and `BksDraft.readTx.UnsafeRange.spec_old`
(today's statements follow: every caller unchanged). `live` is stable while held: only the stop's
commit (`rtRes_cm_close`, under `readTx.Lock()`, the whole `γ.rd`) sets it false.

`backend.Close.spec` is unchanged (`bOpen γ 1`): with no reader holding a share, the clients'
whole token is all it needs (its proof: unchanged, 59 lines; it never needed the readers' shares,
only `stop_take`'s). Its docstring gains: reads begun before it finish first (commit's
`readTx.Lock()`, bbolt's `Close`).

Glue for the auth realization's release (`authBkLife`'s `□ (authRetired ∗ authCur 1 ==∗ K ∗ …)`,
`K = bOpen authOpenQ`): `BksDraft.guarded_RLock` (proved): for any fractional guard `G` with
`G q ⊣⊢ bOpen γ (f q) ∗ (bOpen γ (f q) -∗ G q)` (the currency `Cu q` with the open share inside),
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

Where the pool is built (Q2): the candidate drafted is the constructor,
`BksDraft.backend.newPostK` with `rdPool ∗ rdStock` in place of the replicated `rdTok`s, `rdStock`
the counted remainder (`rdStockN := actualMaxReaders - 2^29 = 2^29` slots) for the clients that
still count (mvcc's `bkRTx`), and `BksDraft.backend.New.spec` under `∀ [ThreadBoundLe GF (2 ^ 29)]`.

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
empty set: `⊢`), timeless, `batchLocked_rbPart` (agreement with `rbData P st.S` on `S ∩ RB`),
`rtHeldF_rbOwnIn` (a held read agrees with the idle part: `∀ n k, S n → P.RB n → vOf P rv n k =
((r.lookup n).getD ∅).lookup k`). Proved over them: `rbOwnIn_set`/`rbPart_set`,
**`rbOwnIn_split_compl`** (the draft premise's `backend.rbOwn_split_in`, restated:
`rbOwnIn γ ⊤ r ⊣⊢ rbOwnIn γ S r ∗ rbOwnIn γ (¬S) r`; the draft's own statement, over `rbOwn`, is
false while a write is pending), `rbOwn_split`, `premise_buckets` (`rbOwnIn ⊤ r ⊢ rbOwnIn
authBkts r ∗ rbOwnIn restNonAuth r`), `rbPutAll_split`, `session_idle`.

Restated statements (each today's, but):
- `batchTxBuffered.UnsafePut.spec`, `UnsafeDelete.spec`: `rbPut` per bucket (the part of the
  bucket written only). Today's form a corollary (`UnsafePut.spec_all`, proved; `rbPutAll`).
  `UnsafeCreateBucket`/`UnsafeDeleteBucket`: the same change, not drafted.
- `batchTxBuffered.Unlock.spec`: extra binders `(S : GoString → Prop) (r)`, `rbPart γ S r` in the
  pre, `Q ∗ rbOwnIn γ S r` in the post (a part handed in comes back idle). Today's a corollary
  (`Unlock.spec_old`, `S := ⊥`, proved).
- `newPostK`: `rbOwnIn γ ⊤ (rbData P D)` in place of `rbOwn γ (rbData P D)` (a fresh backend is
  idle), with the pool (decision 2).

The representation (the Prove phase's): `γ.rbk` a ghost map over the tracked names (the writer's
halves) and a second over the readers' contents, whose client half is in `rbOwnIn` or deposited
in the batch lock by the session's first write to the bucket, a receipt in its place, redeemed by
`Unlock`. The tracked names must be finite (`⊆ P.BT`'s): perhaps a `P.Wf` conjunct.

## Impact (not applied)

With the corollaries, no caller of `RLock`, `UnsafeRange`, `UnsafePut`, `UnsafeDelete` or `Unlock`
must change; what does:

| what | users (modules) | change |
| --- | --- | --- |
| `readTx.UnsafeRange`, `RLock` restated | backend's own proofs (`readTx__RLock`, `readTx__UnsafeRange`) | `RLock`: `rtHeldF_of_open` before returning; `UnsafeRange`: the `live = false` branch goes (`rtHeldF`'s fact) |
| callers of `UnsafeRange.spec` | 9 (applySnapshot, NewServer, SnapApplyWalk, BuildLemmas, StoreBackend, M2StorageDraft{,Restore}, BackendRecs, BackendBridge) | none (corollary); optionally drop the `bOpen` they thread |
| `mvcc.bkRTx := rdTok ∗ bOpen rdOpen`, `rdOpen`, `bOpen_one_shares` | `bkRTx` 8, `rdOpen` 5, `bOpen_one_shares` 2 | Q5: keep, or drop the `bOpen` (`bkRTx := rdTok`), then `rdOpen`/`bOpen_one_shares` go and `BootBackend`'s split of `bOpen 1` with them |
| `rbOwn` (now `rbPart ⊤`) | 14 importing modules; 31 files mention it (13 outside the backend and mvcc are specs) | none by text. The specs taking the whole `rbOwn`: 10 trust-boundary axioms (membership `RaftCluster.Recover`/`SetBackend`, schema `MustSave`/`MustDelete`/`MustReadMembersFromBackend`, v3alarm `NewAlarmStore`/`AlarmStore.restore`, lease `NewLessor`/`lessor.Recover`, auth `NewAuthStore`) and 2 proved (`EtcdServer.restoreAlarms`, `AlarmStore.Recover`, which pass it through): restated over their own buckets' part (Q4), so that the mode-on server can hold only `rbOwnIn restNonAuth` |
| `rbPut` per bucket | 10 (InvBatch, `UnsafePut`/`UnsafeCreateBucket`/`UnsafeDelete`/`UnsafeDeleteBucket` specs and proofs, BackendBridge, CindexBackend, `OnPreCommitUnsafe`, `NewLessor` spec) | proved callers use `rbPut_other`-style (untracked buckets): unchanged; the 4 specs' proofs over the part; `NewLessor`'s (trusted) its bucket's part |
| `Unlock.spec` restated | 8 direct users + backend internals | none (corollary); the auth premise's realization passes `S := authBkts` |
| `newPost`/`newPostK` | 14 / 12 (`BootBackend`, `SnapApplyOpen`, `NewAlloc`, …) | `rbOwnIn ⊤` for `rbOwn` (`rbOwnIn_part` gives today's); the reader stock: `rdPool ∗ rdStock` for `replicate actualMaxReaders rdTok`; mvcc's `New`/`NewStore` count `rdStockN` |
| `New.spec` under `ThreadBoundLe GF (2^29)` | `New`'s callers: `newBackend`→`openBackend`/`bootstrap` → `NewServer`, the snapshot install (`SnapApplyOpen`), the examples' adequacy | each closed result's thread bound `2^31` → `2^29` where `New` is reached (Q2) |
| `rdTok` | 12 | none (still the slot); its counted copies only in `rdStock` |

## The mode-off auth contract (decision 6): who produces it

The producers: the trusted `auth.NewAuthStore` spec (`Proof/go_etcd_io/etcd/server/v3/auth/
NewAuthStore.lean:26`, an axiom) gives the store with `authRecoverOk` (`SnapRO.lean:216`), the
mode-off `Recover` contract, consumed by the snapshot install's `Recover`. A mode-off
`authSchemaSrv` does not exist (today's `AuthSrv.lean` one is mode on). In mode off the permission
checks return early: readers never read the backend (`authReadTxOk` at `.off` names no read
right a client uses). The backend is read only inside `NewAuthStore` (the boot thread, with
`bOpen qo` held) and `Recover` (the apply thread; `bOpen qo` and `mvcc.bkRTx` lent per call and
returned). Recommendation: no guard in mode off; the only change decision 2 brings is
`authRecoverOk`'s `bkRTx` loan, replaced by the pool (`rdPool` ∗ the caller's `threadTok`) when
mvcc moves off counted slots, kept until then.

## The axiom check

No trusted backend spec changes (the restated ones are proved; bbolt's `DB.Close_kv` is
unchanged). The restated semantics were checked against Go anyway (the scratch fork at the pin,
`axiomcx/split_test.go` next to `close_test.go`/`pending_test.go`): a delete then `Unlock`, the
readers no longer see the key (`TestUnlockIdleDelete`); a put below the batch limit then `Unlock`,
seen (`TestUnlockIdlePut`); pending puts and a pending delete on other tracked buckets (lease,
members) leave the auth bucket's contents visible (`TestOtherBucketsPending`); a `ConcurrentReadTx`
begun before `Close` reads, `Close` waiting for it (`TestConcurrentReadBegunBeforeClose`); a held
`readTx` reads repeatedly while `Close` is pending, which does not return before `RUnlock`
(`TestManyReadsWhileClosePending`). All pass; `RLock` after `Close` panics in `UnsafeRange`, as
the acquisition guard requires.

## Review rounds

(below, one section per round)
