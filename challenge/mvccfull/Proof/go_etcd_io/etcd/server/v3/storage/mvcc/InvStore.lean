/-
The store (`kvstore.go`, `kvstore_txn.go`): the backend's contract for the `Key` bucket (the
trust boundary of bbolt and the read buffer), the store's locks and what they hold, and the read
transaction. Lean-first; `notes/decisions.md`, "The transactions: the store's locks and the
backend contract".

**The backend.** `keyReadSnap View RT Del rng rt m L` says `rt` is a `ReadTx` over a snapshot `m` of the
bucket (its `RLock` gives a token under which `UnsafeRange(schema.Key, k, nil, 0)` returns `k`'s
entry of `m`, or nothing: `keyReadLocked`; but for keys compaction may have deleted, `Del`:
`snapThin`); `isKeyBackend b View Del` that `b`'s
`ConcurrentReadTx()`/`ReadTx()` return one of the bucket the caller's `View q m` holds (the
store's ghost map authority at the caller's fraction). `isKeyBackendG` is the general contract,
with the backend's tokens and conditions (`BackendBridge.lean` proves it of the backend);
`isKeyBackend`, mvcc's assumed backend's, its instance without them. The compaction's own calls
(2026-10-13, unit 5a: the deletions, the limited range, the `Meta` bucket's compaction keys, the
safe-range-delete lock) are in the contract under the condition `Cmp`, the backend supporting
mvcc's compaction: true of mvcc's assumed backend; of the real backend not (its model forbids
deletions from the safe-range `Key` bucket: `notes/decisions.md`, "The compaction over the real
backend").

**The locks.** `s.mu` (every transaction holds it shared; exclusively only `store.Compact`)
holds half of `compactMainRev` and a quarter of the compaction revision's authority (`muInv`).
`s.revMu` holds `currentRev` (the committed log's last revision), the other half of
`compactMainRev` and another quarter (`revMuInv`), the index's certificate of the committed log
and the bucket's authority: a reader's snapshot, taken under it, is the committed log's bucket. It also
holds half the revision budget's authority and half the committed log's (`idxLogAuth`; the
writer holds the other halves), so a reader knows its log is above every certificate and leaves
room for the tokens it holds (`store.Read`). A watchable store's (`γ.watchQ`, unit W-K) keeps a
quarter of the committed log's, and the watchable store's `s.mu` the other quarter (`logQ`),
which a commit takes from its caller (`logQPre`/`logQPost`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CutDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.DGhostVar
public import Perennial.Proof.TokSet
public import Perennial.Proof.context
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.context
public import GeneratedProof.go_uber_org.zap
public import Perennial.GeneratedProof.time
public import Perennial.Golang.Theory
public import Code.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.Proof.fmt
public import Spec.go_uber_org.zap.Defs
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Ghost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The real backend's instance** (2026-10-13, unit 5): the store over etcd's backend
(`storage/backend`, proved over bbolt's key-value contract; `BackendBridge.lean`), named by data:
the backend's ghost names `γB`, its parameters but the fixed ones (the clients' bucket table
`BT`, the hook's bound `hookMax`, the batch limit `limit`: the hook's buckets are all but `Key`,
the safe-range bucket is `Key`), the backend's location `be`, and the name `gx` of the batch
lock's late-bound resource (`lateW`: the store registers its own at `NewStore`'s first
`Unlock`); and the compaction mode `cm` (the backend-compaction stage's question 5, Q5-1, the
user's: whether the store over this backend compacts, M2's `ρ.kv.cmp`; `false` for D22's received
backends, "no restore in compaction mode"; `kbCmp` reads it since the core stage's flip). -/
structure KBReal where
  γB : backend.BNames
  BT : GMap GoString w64
  hookMax : Nat
  limit : w64
  be : Loc
  gx : GName
  cm : Bool

/-- **etcd's rest buckets**: the buckets the server's stores keep besides `Key` and `Meta` (the
lessor's `lease`, the alarm store's `alarm`, the auth store's `auth`, `authUsers`, `authRoles`,
the membership's `members`, `members_removed`, `cluster`), which a snapshot's receiver recovers
(D22 S-f). -/
def restBuckets : List GoString :=
  [go!"lease", go!"alarm", go!"auth", go!"authUsers", go!"authRoles", go!"members",
   go!"members_removed", go!"cluster"]

/-- A value the store writes at a compaction key (`RevToBytes(Revision{Main: x})`, `x ≥ 0`). -/
def metaRevVal (v : GoString) : Prop := ∃ x : w64, 0 ≤ sint.Z x ∧ v = revBytes ⟨x, W64 0⟩ false

/-- The backend's parameters of a real instance: the hook's buckets all but `Key`, `Key` the one
safe-range bucket, the hook's own keys the consistent index's two in `Meta` (2026-10-13, unit 7:
only the server's pre-commit hook writes them), the tracked buckets the rest buckets (D22,
2026-10-23: the backend over every bucket), the compaction keys' values the store's revisions
(`metaRevVal`; question 4, 2026-10-29). -/
def KBReal.P (d : KBReal) : backend.BParams :=
  { BT := d.BT, HB := fun n => decide (n ≠ keyName), SB := fun n => decide (n = keyName),
    HK := fun n k => decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧
      (k = go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes)),
    RB := fun n => decide (n ∈ restBuckets),
    hookMax := d.hookMax, limit := d.limit, FV := metaRevVal }

/-- The ghost names of a store: its index's and its bucket's, and its backend's instance (`kb`:
`none`, mvcc's assumed backend contract over the store's own ghost map `bucket`; `some d`, the
real backend). -/
structure StoreNames where
  idx : IdxNames
  bucket : GName
  /-- `ghostVar Log`: the committed log, half under `s.revMu`, half the writer's state's (`writerL`,
  in `writerInv`; until D22 receiver epochs S2 under the batch lock) -/
  clog : GName
  /-- the lessor's ghost map (`lease.lessorMu`): its live set, half the lease owner's
  (`lease.leaseOwn`, what `Attach` needs), and its location -/
  leases : GName
  /-- the revision budget (`ownTokAuth`): a write transaction costs one token (`revToken`), so
  `currentRev` never overflows -/
  revs : GName
  /-- the batch lock's invariant `P` (a saved proposition, read-only): the backend's
  `LockInsideApply` runs the post-lock hook with it (`hookIs`) -/
  hook : GName
  /-- the post-lock hook's function value `f` (`dghostVar`, read-only) -/
  hookFn : GName
  /-- the backend's instance: `none`, mvcc's assumed contract; `some d`, the real backend -/
  kb : Option KBReal
  /-- the meta keys `scheduledCompactRev` and `finishedCompactRev` as the store wrote them
  (`metaCompact`, a ghost variable in the batch lock's resource) -/
  cmeta : GName
  /-- the finished compactions' revision (a monotone counter of `crevN`; `compactedAt` is a
  lower bound of it) -/
  fin : GName
  /-- the compaction scheduler's names (`schedule.isScheduler`) -/
  sch : schedule.SchedNames
  /-- the committed logs' certificates of the caller's (2026-10-14, unit T1): a ghost map from a
  log's length to the log (persistent elements, `certOk`), whose authority `NewStore` hands its
  caller; every committed log beyond `NewStore`'s two revisions has one (`revMuInv`), which the
  writer supplies at the commit (`txnEndPre`) and a reader learns of the log it read
  (`store.Read`). The etcd server's elements say a log is the KV model of a committed raft log. -/
  cok : GName
  /-- the store is a watchable store's (the watch slice's unit W-K, fixed by `NewStore`'s caller):
  `s.revMu` then holds a quarter of the committed log's authority and the watchable store's
  `s.mu` the outer quarter (`logQ`), which a commit takes from its caller; otherwise `s.revMu`
  holds a half and a commit needs nothing more (`revQ`, `logQPre`) -/
  watchQ : Bool
  /-- (D22 receiver epochs, S2, 2026-10-22) the writer's deposit (`ghostVar Unit`): `s.mu`'s
  resource holds it at its fraction (`muInv`); a writer, holding `s.mu` shared, deposits its part
  in the writer's invariant while it holds the writer's state (`wDep`, `writerInv`), so the holder
  of `s.mu` exclusively finds that state there -/
  wr : GName := 0
  /-- (S2) the batch lock's key (`ghostVar Unit`, exclusive: `writerKey`), in the batch lock's
  resource or deposited by the writer holding the lock; per backend -/
  wk : GName := 0
  /-- (S2) the log the batch lock's view is of (`ghostVar Log`): half in the batch lock's resource
  (`writerRes`), half in the writer's state (`writerL`); per backend -/
  wv : GName := 0
  /-- (D22 receiver epochs, S3, 2026-10-22; S5b) the store's current objects and physical names
  (`dghostVar (StoreObjs × PhysNames)`: the values of the four fields `store.Restore` writes and the
  ghost names of the backend, index and scheduler they are; `curAt`): fractions of it in every share
  of the locks guarding their readers (`fieldShare`, `revMuBody`, `writerInv`, `readerPool`) and the
  writer's fragment (`writerFrag`), so that they agree, and `store.Restore`, gathering them all, can
  move it (S3 to S5b: a discarded pin of the objects, `objsPin`) -/
  cur : GName := 0
  /-- (D22 receiver epochs, S3) `s.revMu`'s restoring flag (`dghostVar Bool`): half in `s.revMu`'s
  resource (`revMuInv`, restoring: `store.Restore` releases `s.revMu` with `currentRev = 1` before
  the restored revision is known), half in the shares of the fields (`fieldShare`), so that a
  reader holding `s.mu` or a watchable store's `s.mu` finds it not restoring -/
  rst : GName := 0
  /-- (D22 receiver epochs, S4, 2026-10-22) the readers' tickets (`ownTokAuth`): an idle reader
  holds one (`storeReaderC`), the readers' pool the authority over those it has a slot for -/
  tk : GName := 0
  /-- (S4) the checked-out tickets (`ownTokAuth`): a transaction holds one while it has a slot of
  the pool, the pool the authority -/
  tko : GName := 0
  /-- (D22 receiver epochs, S5a, 2026-10-22) the watchable store's deposit ghost (`ghostVar Unit`):
  the watchable store's `s.mu` holds it at its fraction (`wsFields`); `syncWatchers`, holding that
  lock, deposits all of it in the readers' pool while it has a slot out (`wsDep`), so the holder of
  that lock (`store.Restore`'s caller) finds no slot out under it -/
  wsd : GName := 0
  /-- (S5a) the tickets checked out under the watchable store's lock (`ownTokAuth`) -/
  tkw : GName := 0
  /-- (the restore plan's R5e) the retired tickets (`ownTokAuth`): a reader that retires its ticket
  for a backend token of its own (`readerPool_retire`) holds one, the readers' pool the authority,
  so that the pool's slots and the retired readers' tokens are at most `nReaders` together -/
  tkr : GName := 0
  /-- (question 5's wiring, the write right's home, 2026-10-29; physical) the compaction keys' write
  right's lock key (`ghostVar Bool`): half in the batch lock's resource (`mwSlot`, when the store
  compacts), half in the write right's invariant (`mwInv`), recording where the right is -/
  mwk : GName := 0
  /-- (M2, the storage side, 2026-10-30: review round 3's S2.5, the user's approval item 26;
  logical) the store's compaction mode, set by `NewStore` (`decide (kbCmpM kb)`), kept by
  `withPhys` (a restore keeps the mode), tied to the current backend by `physOk` (`kbCmpM γ.kb ↔
  γ.cm = true`): what the logical predicates gated by the mode read (`wsFrozenM`, `crevRightM`),
  so that they do not move when `store.Restore` installs a backend -/
  cm : Bool := false
  /-- (M2, the storage side, review round 4's S2.2, the approval's item 34; physical) the agreement
  name of the scheduler's payload (`stopPayAt`): fresh per scheduler, it records the store's stop
  channel, which `NewStore`/`store.Restore` make after the scheduler -/
  sx : GName := 0
  /-- (C3's store law, 2026-11-02; logical) the compaction revisions' permit (`savedPredOwn`,
  read-only, `crevPermIs`): a predicate fixed when the store is created (`True` for a caller that
  does not care); `withPhys` keeps it, so a restore's names agree with `NewStore`'s -/
  cperm : GName := 0
  /-- (the mvcc API, stage 1, 2026-11-03; strict M1, 2026-11-04, `notes/decisions.md`, "strict
  M1, no scaffold") the API's ghost names (`api.AbsNames`: the client's view, the pending revision,
  the compaction authority, the share token, the frozen flag), which the slots (`slotX`, `slotY`,
  `slotF`, `slotFr`, `slotFl`) hold; logical, `withPhys` keeps it -/
  api : api.AbsNames := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  /-- (the snapshot image's (c), 2026-11-05; physical) the meta keys' records' compaction revision
  (`ghostVar Int`, a compacting real backend's): half in the batch lock's resource (`compactRes`'s
  `cmpTrack`, at the records' `CmpRecs.crev`), half in the writer's slot (`slotY`, at its view's
  compaction revision), so that the holder of the writer's state sees the records restore to the
  API's compaction revision (`mvccImage_snapshot.law`) -/
  rcv : GName := 0
  /-- (the snapshot image's tracking, the job, 2026-11-06; physical) the compaction job's cursor
  (`ghostVar (Int × Rev)`, a compacting real backend's): half in the batch lock's resource
  (`cmpTrack`, the last job's revision and position, `snap.cmpOk`'s `jc`), half the compactor's
  (`compactTok`'s `jobCur`, handed from job to job), so that a job finds its own cursor between its
  batches -/
  jc : GName := 0
  /-- (the job, 2026-11-06; physical) the records' compaction revision's lower bounds
  (`monoNatAuthOwn` of `crevN`): the authority in the batch lock's resource (`cmpTrack`), a lower
  bound minted by `updateCompactRev` at the revision it schedules (`cmpLb`, in the job's premise),
  so that the job's revision is at most the records' -/
  rcl : GName := 0

instance idxNames_countable : Pos.Countable IdxNames :=
  countableOfLeftInverse (fun x : IdxNames => (x.hist, x.nev, x.log, x.crev, x.cmp))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

instance schedNames_countable : Pos.Countable schedule.SchedNames :=
  countableOfLeftInverse (fun x : schedule.SchedNames => (x.run, x.jobs, x.pay))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

instance dbNames_countable : Pos.Countable backend.DBNames :=
  countableOfLeftInverse (fun x : backend.DBNames => (x.db, x.wr)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance bNames_countable : Pos.Countable backend.BNames :=
  countableOfLeftInverse
    (fun x : backend.BNames => ((x.dls, x.fkd, x.dbf, x.rq), x.rbD, (x.fkv, x.fk, x.dlb, x.dlg, x.cln, x.rbk, x.hkd, x.db, x.view, x.rd, x.hist, x.cached, x.cur, x.hook,
      x.opn, x.wb, x.rdt, x.txa, x.txb, x.rvs, x.cvw, x.wbc, x.used, x.cls, x.sdn, x.stk)))
    (fun pr0 => let pr := pr0.2; let r0' := pr.2; let r := r0'.2; let r' := r.2; let r0 := r'.2; let q0 := r0.2; let q := q0.2; let p := q.2; ⟨p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, p.1, q.1, q0.1, r0.1, r'.1, r.1, r0'.1, pr0.1.2.2.1, pr0.1.2.2.2, pr.1, pr0.1.2.1, pr0.1.1⟩)
    (fun _ => rfl)

instance kbReal_countable : Pos.Countable KBReal :=
  countableOfLeftInverse (fun x : KBReal => (x.γB, x.BT, x.hookMax, x.limit, x.be, x.gx, x.cm))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

instance storeNames_countable : Pos.Countable StoreNames :=
  countableOfLeftInverse
    (fun x : StoreNames => (((((((x.idx, x.bucket, x.clog, x.leases, x.revs, x.hook, x.hookFn, x.kb, x.cmeta, x.fin, x.sch, x.cok, x.watchQ, x.wr, x.wk, x.wv, x.cur, x.rst, x.tk, x.tko, x.wsd, x.tkw), x.tkr), x.mwk), x.cm, x.sx), x.cperm), x.api), (x.rcv, x.jc, x.rcl)))
    (fun r3 => let r2 := r3.1; let r1 := r2.1; let r0 := r1.1; let r := r0.1; let q := r.1; let p := q.1; ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, q.2, r.2, r0.2.1, r0.2.2, r1.2, r2.2, r3.2.1, r3.2.2.1, r3.2.2.2⟩)
    (fun _ => rfl)

/-- **The store's physical ghost names** (D22 receiver epochs, S5b, 2026-10-22): those of one
backend (`kb`, the bucket's view `bucket`, the batch lock's invariant `hook` and the hook
`hookFn`, the batch lock's key `wk` and view log `wv`, the compaction's meta keys `cmeta` and
finished counter `fin`, the write right's lock key `mwk`), one index (`nev`, `cmp`) and one scheduler (`sch`): what `store.Restore`
replaces. The current ones are the store's ghost variable `cur`'s (`curAt`), and a predicate
over the store's names `γ` reads them as `γ`'s own (`StoreNames.withPhys`). -/
structure PhysNames where
  nev : GName
  cmp : GName
  bucket : GName
  hook : GName
  hookFn : GName
  kb : Option KBReal
  cmeta : GName
  fin : GName
  sch : schedule.SchedNames
  wk : GName
  wv : GName
  mwk : GName
  /-- (M2, the storage side, item 34) the scheduler's payload's agreement name (`stopPayAt`) -/
  sx : GName
  /-- (the snapshot image's (c)) the records' compaction revision (`StoreNames.rcv`) -/
  rcv : GName
  /-- (the job, 2026-11-06) the job's cursor and the records' lower bounds (`StoreNames.jc`, `rcl`) -/
  jc : GName
  rcl : GName

instance physNames_countable : Pos.Countable PhysNames :=
  countableOfLeftInverse
    (fun x : PhysNames => (((x.nev, x.cmp, x.bucket, x.hook, x.hookFn, x.kb, x.cmeta, x.fin, x.sch, x.wk, x.wv), x.mwk, x.sx), (x.rcv, x.jc, x.rcl)))
    (fun q' => let q := q'.1; let p := q.1; ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2, q.2.1, q.2.2, q'.2.1, q'.2.2.1, q'.2.2.2⟩)
    (fun _ => rfl)

/-- The physical names of the store's names `γ`. -/
def StoreNames.phys (γ : StoreNames) : PhysNames :=
  ⟨γ.idx.nev, γ.idx.cmp, γ.bucket, γ.hook, γ.hookFn, γ.kb, γ.cmeta, γ.fin, γ.sch, γ.wk, γ.wv, γ.mwk,
    γ.sx, γ.rcv, γ.jc, γ.rcl⟩

/-- **The store's names `γ` at the physical names `p`** (S5b): the logical names `γ`'s. -/
def StoreNames.withPhys (γ : StoreNames) (p : PhysNames) : StoreNames :=
  ⟨⟨γ.idx.hist, p.nev, γ.idx.log, γ.idx.crev, p.cmp⟩, p.bucket, γ.clog, γ.leases, γ.revs, p.hook,
    p.hookFn, p.kb, p.cmeta, p.fin, p.sch, γ.cok, γ.watchQ, γ.wr, p.wk, p.wv, γ.cur, γ.rst, γ.tk,
    γ.tko, γ.wsd, γ.tkw, γ.tkr, p.mwk, γ.cm, p.sx, γ.cperm, γ.api, p.rcv, p.jc, p.rcl⟩

/-- **The store's objects** (D22 receiver epochs, S3, 2026-10-22): the values of the four fields
`store.Restore` writes (`s.b`, `s.kvindex`'s tree index, `s.fifoSched`, `s.stopc`). Their
points-to are shared by the locks that guard their readers (`storeFields`, `fieldShare`), not
persistent; which objects they are is the store's ghost variable `cur`'s (`curAt`; S3 to S5b, a
discarded pin, `objsPin`). -/
structure StoreObjs [GooseExts] where
  b : GoInterface
  ti : Loc
  ssched : GoInterface
  sstop : Loc

instance storeObjs_countable [GooseExts] : Pos.Countable StoreObjs :=
  countableOfLeftInverse (fun x : StoreObjs => (x.b, x.ti, x.ssched, x.sstop))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the store's `mu`. -/
abbrev muAddr (s : Loc) : Loc := structFieldRef store go!"mu" s
/-- The address of the store's `revMu`. -/
abbrev revMuAddr (s : Loc) : Loc := structFieldRef store go!"revMu" s
/-- The address of a `storeTxnRead`'s embedded `storeTxnCommon`. -/
abbrev txCommon (tr : Loc) : Loc := structFieldRef storeTxnRead go!"storeTxnCommon" tr

end addrs

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ### The API's slots (stage 1; strict M1, 2026-11-04)

The locks' resources hold every fraction of the ghost state they tie together, so the API's ghost
state (`Api/Ghost.lean`) is tied to the committed log inside them: `s.revMu`'s body holds
`slotX γ q log c`, the writer's state `slotY γ ilog`, the writer's invariant a frozen state
(`slotFl`, `slotF`) and the restorer's deposit (`slotFr`), all at the store's names' `api`. -/

/-- **`s.revMu`'s slot**: the API's quarter of `q` of the view and of the compaction authority. -/
def slotX (γ : StoreNames) (q : Qp) (L : Log) (c : Int) : IProp GF := api.revMuAbs γ.api q L c

/-- The writer's part of the pending revision (§1): a quarter for a watchable store (another
quarter is `watchStoreBody`'s), half for a plain one. -/
def pndW (γ : StoreNames) : Qp := if γ.watchQ then (1 : Qp).half.half else (1 : Qp).half

/-- **The records' compaction revision's part `q`** (`StoreNames.rcv`; the snapshot image's (c),
2026-11-05): a compacting real backend's ghost variable at `c`, nothing otherwise. -/
def rcvW (γ : StoreNames) (q : Qp) (c : Int) : IProp GF :=
  match γ.kb with
  | some d => if d.cm = true then ghostVar γ.rcv q c else iprop(True)
  | none => iprop(True)

/-- **The writer's state's slot**: the API's writer quarter of the view and its part of the
pending revision at `none`, with (the snapshot image's (c)) the writer's half of the records'
compaction revision at the view's compaction revision. -/
def slotY (γ : StoreNames) (L : Log) : IProp GF :=
  iprop(∃ c : Int, api.absPart γ.api (1 : Qp).half.half L c ∗ api.pndPart γ.api (pndW γ) none ∗
    rcvW γ (1 : Qp).half c ∗ api.wcrPart γ.api (1 : Qp).half c)

/-- **The frozen state's deposit**: the whole backend share token. -/
def slotF (γ : StoreNames) : IProp GF := api.shareTok γ.api 1

/-- **The restorer's deposit**: the whole backend share token. -/
def slotFr (γ : StoreNames) : IProp GF := api.shareTok γ.api 1

/-- **The frozen flag's part `q` at `b`.** -/
def slotFl (γ : StoreNames) (q : Qp) (b : Bool) : IProp GF := ghostVar γ.api.frz q b

/-- **The store's current objects and physical names are `o` and `γ`'s**, at the fraction `dq`
(D22 receiver epochs, S5b: until then `objsPin`, a discarded pin of the objects): a part of the
store's ghost variable `cur`, which every share of the locks guarding a reader of the objects holds
(`fieldShare`, `revMuBody`, `writerInv`, `readerPool`) and the writer's fragment (`writerFrag`),
so that they agree on them, and `store.Restore`, which gathers them all, can move them. A
predicate at names `γ` with such a part is of the current backend, index and scheduler. -/
def curAt (γ : StoreNames) (dq : DFrac) (o : StoreObjs) : IProp GF :=
  dghostVar γ.cur dq ((o, γ.phys) : StoreObjs × PhysNames)

/-- **A real backend's `meta` bucket records no compaction** (opaque, exclusive; D22 S-g,
2026-10-19, D19l (v) (A); until then the opaque `Prop` `backendNoCompaction`, a premise of
`NewStore` ... `NewServer.spec` and of the closed theorems): the bbolt data of the backend `γB`
holds neither the scheduled nor the finished compaction's key (`schema.ScheduledCompactKeyName`,
`FinishedCompactKeyName`), and only a store over it writes them (its compaction:
`UnsafeSetScheduledCompact` in `store.Compact`, `UnsafeSetFinishedCompact` in the job). The
store's `restore` consumes it (it reads both keys, `kvstore.go:330-342`: a finished one sets
`compactMainRev`, a scheduled one above it raises `currentRev` and resumes the compaction). The
readers' view of a backend leaves out every bucket but `Key` (`bridgeParams`), so the model
cannot state the `meta` bucket's keys to the store: this names the fact about the backend's data,
as `etcdserver.bkFresh` does a fresh bucket's, given by whoever opens the backend over data of
which it is true: `bootstrap`'s contract for a new cluster's backend (a bbolt file created empty,
`bootOk`), and for a received image the opener of a data `D` without either key (`keyImage`'s
last two conjuncts, `Image.lean`; D22 S-j). Defined since the backend-compaction stage
(2026-10-29; until then opaque, and the axiom `kbNoCmp_metaNone` gave its reads): the client's half
of the backend's compaction-key flag at `0` (`backend.fkOwn`), which the backend's constructor gives
over such data (`bkNoCmp_of_fkCl`), and under which a held reader's state has neither key
(`backend.fkRd_abs`). (M3, 2026-11-06) At known values: the flag at `0` (`backend.fkFlag`) with the
client's halves of the compaction keys' values at none and of the deleted entries at none (the
open's, `backend.fkCl_exact`), so that `NewStore` deposits the values in its tracked compaction
and lends `restore` the flag alone (`bkNoCmpF`). -/
def bkNoCmp (γB : backend.BNames) : IProp GF :=
  iprop(backend.fkFlag γB 0 ∗ backend.fkdOwn γB (none, none) ∗
    backend.dlsOwn γB (∅ : GMap (GoString × GoString) GoString))

/-- **mvcc's assumed backend's compaction-key flag** (`kb = none`, the store's own ghost map
`γb`; question 5's wiring, (iii), 2026-10-29): opaque, the assumed backend's counterpart of the real
backend's `backend.fkOwn` (`0`: neither compaction key recorded), given by that backend's creator. -/
opaque viewFk (γb : GName) (f : Nat) : IProp GF

/-- The same as `bkNoCmp` for mvcc's assumed backend: its flag at `0` (`viewFk`; until question 5's
wiring, 2026-10-29, opaque itself), given by that backend's creator with its fresh key bucket (no
caller in this repository). -/
def viewNoCmp (γb : GName) : IProp GF := viewFk γb 0

/-- **The backend of the instance `kb` records no compaction** (`bkNoCmp`, `viewNoCmp`): what
`restore` consumes in place of the opaque premise `backendNoCompaction` (D22 S-g). -/
def kbNoCmp (kb : Option KBReal) (γb : GName) : IProp GF :=
  match kb with
  | none => viewNoCmp γb
  | some d => bkNoCmp d.γB

/-- **The real backend's write right at its values** (the contract's `MW w X`; the snapshot
image's (b), 2026-11-05): the client's half of the compaction-key flag (at some value) with the
client's halves of the compaction keys' values `w` (`backend.fkdOwn`) and of the safe-range buckets'
deleted entries `X` (`backend.dlsOwn`): `backend.fkOwn` with its values exposed, which the
contract's delete and `Meta` put move exactly (`dlStep`, `fkPutV`). -/
def bkMW (γB : backend.BNames) (w : backend.FkVals) (X : backend.VData) : IProp GF :=
  iprop((∃ f : Nat, monoNatAuthOwn γB.fk (1 : Qp).half f) ∗ backend.fkdOwn γB w ∗
    backend.dlsOwn γB X)

/-- **The write right at its values in the instance `kb`** (the contract's `MW`): the real
backend's `bkMW`; for mvcc's assumed backend, its flag at any value (the values not tracked). -/
def kbMWv (kb : Option KBReal) (γb : GName) (w : backend.FkVals) (X : backend.VData) : IProp GF :=
  match kb with
  | none => iprop(∃ f : Nat, viewFk γb f)
  | some d => bkMW d.γB w X

/-- **The write right's flag part** (the snapshot image's (a), 2026-11-05): what the write right's
invariant (`mwInv`) keeps, the client's half of the compaction-key flag; the values' halves
(`kbVals`) are the batch lock's resource's (`compactRes`'s `cmpTrack`), pinned at the store's
records. -/
def kbMWf (kb : Option KBReal) (γb : GName) : IProp GF :=
  match kb with
  | none => iprop(∃ f : Nat, viewFk γb f)
  | some d => iprop(∃ f : Nat, monoNatAuthOwn d.γB.fk (1 : Qp).half f)

/-! ## The backend's contract -/

/-- **A read capability** (persistent): a slice `s` a read returned as holding `b` (`Rd s b`)
can be read while the reader's token `Tok` is held, at some fraction, the token lent out
meanwhile. The slices of a real backend are bbolt's, valid only while its read transaction
lives (until the reader's `RUnlock`, or while the batch transaction's lock is held): what the
backend's `rdB rtx` with `crtSnap_read`/`rtHeld_read`, and the batch transaction's `UnsafeRange`
capability under `batchLocked`, give. -/
def rdCap (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) : IProp GF :=
  iprop(□ ∀ (s : GoSlice) (b : GoString), Rd s b -∗ Tok -∗
    ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ Tok))

/-- **Two slices read at once under `Tok`** (the backend-compaction stage, 3.5; Draft,
2026-10-28): as `rdCap`, for a pair (the compaction job hashes a key and its value together,
`h.WriteKeyValue(keys[i], values[i])`). -/
def rdCap2 (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) : IProp GF :=
  iprop(□ ∀ (s1 s2 : GoSlice) (b1 b2 : GoString), Rd s1 b1 -∗ Rd s2 b2 -∗ Tok -∗
    ∃ dq1 dq2 : DFrac, s1 ↦*{dq1} b1 ∗ s2 ↦*{dq2} b2 ∗ (s1 ↦*{dq1} b1 -∗ s2 ↦*{dq2} b2 -∗ Tok))

/-- What `UnsafeRange(Key, k, nil, 0)` returns of the bucket `m`: the key and its value if `m`
has `k` (read-only outer slices, the inner ones readable through `Rd`), else no key and no
value. -/
def keyVals (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice) (m : Bucket) (k : GoString) :
    IProp GF :=
  match m.lookup k with
  | some v => iprop(∃ (ksl vsl : GoSlice), ks ↦*□ [ksl] ∗ □ Rd ksl k ∗ vs ↦*□ [vsl] ∗ □ Rd vsl v)
  | none => iprop(ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice))

/-- `rt`'s `UnsafeRange(schema.Key, key, nil, 0)`, for `key` holding `k`, under the reader's
token `Tok`, reads `k`'s entry of the snapshot `m` (its slices readable through `Rd`). -/
def keyRangeSpec (rt : GoInterfaceOk) (m : Bucket) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Tok ∗ key ↦*{dq} k }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ key ↦*{dq} k ∗ keyVals Rd ks vs m k }})

/-- The slices `ks` and `vs` (read-only, of slices readable through `Rd`) hold the keys and the
values of the entries `l`, in order. -/
def pairVals (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice)
    (l : List (GoString × GoString)) : IProp GF :=
  iprop(∃ kss vss : List GoSlice, ks ↦*□ kss ∗ vs ↦*□ vss ∗
    ⌜kss.length = l.length ∧ vss.length = l.length⌝ ∗
    [∗list] i ↦ p ∈ l, ∃ ksl vsl : GoSlice, ⌜kss[i]? = some ksl ∧ vss[i]? = some vsl⌝ ∗
      □ Rd ksl p.1 ∗ □ Rd vsl p.2)

/-- What `UnsafeRange(Key, lo, hi, 0)` returns of the bucket `m` (`hi` not empty): the entries
with a key in `[klo, khi)`, in key order (`bucketRange`; no limit). -/
def rangeVals (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice) (m : Bucket)
    (klo khi : GoString) : IProp GF :=
  pairVals Rd ks vs (bucketRange m klo khi)

/-- `rt`'s `UnsafeRange(schema.Key, lo, hi, 0)`, for `lo` holding `klo` and `hi` holding a
non-empty `khi`, under the reader's token `Tok`, reads the entries of the snapshot `m` with a
key in `[klo, khi)`, in key order (bbolt's cursor from `klo` while below `khi`; the limit `0` is
none). -/
def keyRangeReadSpec (rt : GoInterfaceOk) (m : Bucket) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (lo hi : GoSlice) (klo khi : GoString) (dqlo dqhi : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Tok ∗ lo ↦*{dqlo} klo ∗
        hi ↦*{dqhi} khi ∗ ⌜khi ≠ []⌝ }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #lo))
        (Val #hi)) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ lo ↦*{dqlo} klo ∗ hi ↦*{dqhi} khi ∗
        rangeVals Rd ks vs m klo khi }})

/-- `rt`'s `UnsafeRange(schema.Key, lo, hi, limit)` with any `limit` (the restore plan's R4b), for
`lo` holding `klo` and `hi` a non-empty `khi`, under the reader's token `Tok`: entries of the
snapshot `m` with a key in `[klo, khi)`, in key order, some of them: a sublist of the range (with
`n` entries in the read buffer the real read returns bbolt's first `limit - n`, then the buffer's,
`nonissues/etcd-unsafe-range-limit-buffer.md`; all of them with no limit, `keyRangeReadSpec`). -/
def keyRangeLimSpec (rt : GoInterfaceOk) (m : Bucket) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) (cl : Bool := false) : IProp GF :=
  iprop(∀ (b : GoInterface) (lo hi : GoSlice) (klo khi : GoString) (dqlo dqhi : DFrac) (lim : w64),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Tok ∗ lo ↦*{dqlo} klo ∗
        hi ↦*{dqhi} khi ∗ ⌜khi ≠ []⌝ }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #lo))
        (Val #hi)) (Val #lim))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ lo ↦*{dqlo} klo ∗ hi ↦*{dqhi} khi ∗
        ∃ res : List (GoString × GoString), pairVals Rd ks vs res ∗
          ⌜res.Sublist (bucketRange m klo khi) ∧
            (cl = true → 0 < sint.Z lim → res = (bucketRange m klo khi).take (sint.Z lim).toNat)⌝ }})

/-- The bytes of `schema.ScheduledCompactKeyName` (`"scheduledCompactRev"`). -/
def schedKeyBytes : GoString := go!"scheduledCompactRev"
/-- The bytes of `schema.FinishedCompactKeyName` (`"finishedCompactRev"`). -/
def finKeyBytes : GoString := go!"finishedCompactRev"

/-- The `Meta` bucket's two compaction keys (the store's: nothing else writes them). -/
def metaCompactKey (kn : GoString) : Prop := kn = schedKeyBytes ∨ kn = finKeyBytes

/-- `rt`'s `UnsafeRange(schema.Meta, key, nil, 0)` at a compaction key, under the reader's token
`Tok`: nothing, or the key and a value the store wrote there (`metaRevVal`; which one is not
modelled: the store's own record is `metaCompact`, under the batch lock), their slices readable
through `Rd` while `Tok` is held (`rdCap`, the backend's lent slices; the backend-compaction stage,
2026-10-29: until then read-only for good, at no token). With `nc` (a backend that records no
compaction: `keyReadLocked`'s clause under `kbNoCmp`), nothing. -/
def metaReadSpec (rt : GoInterfaceOk) (nc : Bool) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (kn : GoString) (dq : DFrac),
    ⌜metaCompactKey kn⌝ →
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ Tok ∗ key ↦*{dq} kn }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); Tok ∗ key ↦*{dq} kn ∗
        ((ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) ∨
          ∃ (ksl vsl : GoSlice) (v : GoString), ⌜nc = false⌝ ∗ ks ↦*□ [ksl] ∗ Rd ksl kn ∗
            vs ↦*□ [vsl] ∗ Rd vsl v ∗ ⌜metaRevVal v⌝) }})

/-- A snapshot `m'` of the bucket `m` with some of the keys compaction may delete missing
(`Del`, the store's: `delKey`): the backend's reads after the compaction's `UnsafeDelete`s
(committed or written back) do not see them. -/
def snapThin (m m' : Bucket) (Del : GoString → IProp GF) : IProp GF :=
  iprop(⌜∀ k v, m'.lookup k = some v → m.lookup k = some v⌝ ∗
    □ (∀ k v, ⌜m.lookup k = some v ∧ m'.lookup k = none⌝ -∗ Del k))

/-- A `ReadTx` as the compaction's `checkPrevCompactionCompleted` uses it, with no view of the
bucket (it holds neither of the store's locks that hold the view): `RLock` gives a reader's token
`Tok`, under which its reads of the `Meta` bucket's compaction keys (`metaReadSpec`) lend their
slices (`rdCap`), and `RUnlock` takes it (the backend-compaction stage, 2026-10-29: until then
`RLock`/`RUnlock` at `True` and the reads at no token, which the real backend cannot meet), for
the reader's budget token `RT` (as `keyReadSnap`'s `RLock`/`RUnlock`; question 4's round,
2026-10-29: until then none, which the real backend's `RLock` cannot meet either). -/
def metaReadTx (rt : GoInterfaceOk) (RT : IProp GF) : IProp GF :=
  iprop(□ ({{ RT }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); ∃ (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF), Tok ∗ rdCap Rd Tok ∗
        □ metaReadSpec rt false Rd Tok ∗
        □ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) }}))

/-- **Two readers of one read transaction** (the restore plan's R5b): its token splits into a
part that ranges and reads (`TokA`) and one that reads (`TokB`: `restore`'s goroutine reads the
keys `restore` sent while `restore` goes on ranging), joined back before `RUnlock`. -/
def rdSplit (rt : GoInterfaceOk) (m : Bucket) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF) (cl : Bool) : IProp GF :=
  iprop(Tok -∗ ∃ TokA TokB : IProp GF, TokA ∗ TokB ∗ rdCap Rd TokA ∗ rdCap Rd TokB ∗
    □ keyRangeLimSpec rt m Rd TokA cl ∗ (TokA -∗ TokB -∗ Tok))

/-- `rt` locked, over the snapshot `m` of the bucket (persistent), with `Tok` the reader's
token from its `RLock` to its `RUnlock`: `RUnlock` takes `Tok` and gives back the reader's
budget token `RT` (`isKeyBackendG`), and under `Tok` its reads are the snapshot's: a key's
entry (`keyRangeSpec`) and, if `rng`, a range of keys (`keyRangeReadSpec`; with a limit,
`keyRangeLimSpec`), their slices readable
through `Rd` while `Tok` is held (`rdCap`); and, if `rng`, with `NC` (the store's: its backend
records no compaction, `kbNoCmp`) its reads of the `Meta` bucket's compaction keys find nothing
(`metaReadSpec … true`; given back: the backend-compaction stage, 2026-10-29, in place of the axiom
`kbNoCmp_metaNone`). (`rng` is false for a `ConcurrentReadTx`, whose range
of a safe-range bucket can return a key twice over a stale cached read buffer: 2026-10-13, unit 5,
`nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`.) -/
def keyReadLocked (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) : IProp GF :=
  iprop(□ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) ∗
    □ keyRangeSpec rt m Rd Tok ∗
    (if rng then iprop(□ keyRangeReadSpec rt m Rd Tok ∗ □ keyRangeLimSpec rt m Rd Tok cl ∗
      □ rdSplit rt m Rd Tok cl ∗ □ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok))
     else iprop(True)) ∗
    rdCap Rd Tok)

/-- `rt` is a `ReadTx` over the snapshot `m` of the bucket the caller's view holds
(persistent), with `L` the right to lock it: `RLock`, with the caller's view `View q m` (any
fraction; the caller keeps it), turns `L` into the reader's token `Tok`, over which `rt` is
locked (`keyReadLocked`: the slices' predicate `Rd` and the token are chosen by the lock, for a
shared read transaction reads the bbolt transaction of the interval its `RLock` finds). A
concurrent read transaction's `RLock` does nothing (`L = Tok`, the view unused); the shared
one's takes its read lock, the view tying what it reads to `m` (2026-10-13, the backend bridge:
the shared transaction's state is the one at its `RLock`, not at `ReadTx()`). What it reads is
`m` but for some keys compaction may have deleted (`snapThin m m' Del`: 2026-10-13, unit 5a; the
real backend's snapshots are exact). -/
def keyReadSnap (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) (Del : GoString → IProp GF)
    (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) : IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (m' : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ keyReadLocked RT NC rng rt m' Rd Tok ∗ snapThin m m' Del }}))

/-! ## The post-lock hook -/

/-- The real backend's post-lock hook is the Go function `f` for good (`plHookRO`), not `nil`. -/
def bkHookIs (γB : backend.BNames) (f : val) : IProp GF :=
  iprop(∃ g : GoFunc, ⌜f = #g ∧ g ≠ func.nil⌝ ∗ backend.plHookRO γB g)

/-- **The post-lock hook is `f` for good** in the backend instance `kb` (persistent; unit N4,
D14b): for mvcc's assumed backend, the store's own read-only ghost variable `hfn` (`NewStore`
allocates it at its caller's `f`); for the real backend, the backend's own slot frozen at the Go
function `f` (`backend.plHookRO`: the etcd server installs the hook after creating the store,
`server.go:412`, and freezes it then), not `nil`. -/
def kbHookIs (kb : Option KBReal) (hfn : GName) (f : val) : IProp GF :=
  match kb with
  | none => dghostVar hfn DFrac.discard f
  | some d => bkHookIs d.γB f

/-- The store's post-lock hook fact, as a predicate of the hook (`batchTxSpecG`'s `HF`). -/
abbrev hookFn (γ : StoreNames) : val → IProp GF := kbHookIs γ.kb γ.hookFn

/-- **The post-lock hook at `nil`, at the share `dq`** (§4.8, a store without a hook, 2026-11-06):
`batchTxSpecG`'s `HN` at the store, `LockInsideApply`'s nil arm taking any share of the hook at `nil`
(the backend's spec does): the client's half (`kbHookNil`, until the server sets the hook), or the
hook frozen at `nil` (`DFrac.discard`: a store the server never sets a hook on, the tester's). -/
def kbHookNilAt (kb : Option KBReal) (dq : DFrac) : IProp GF :=
  match kb with
  | none => iprop(False)
  | some d => backend.plHookAt d.γB dq func.nil

/-- **The batch lock's invariant** `P` of the store (persistent; a saved proposition, so that a
caller naming it agrees with the store's). -/
def hookP (γ : StoreNames) (P : IProp GF) : IProp GF := savedPropOwn γ.hook DFrac.discard P

/-! ## The batch transaction -/

/-- The entries a batch transaction has put into the `Key` bucket since it was locked, in
order (`UnsafeSeqPut`). -/
abbrev Puts := List (GoString × GoString)

/-- The lessor's `Lease` bucket's name (`schema.leaseBucketName`). -/
abbrev leaseName : GoString := go_etcd_io.etcd.server.v3.storage.schema.leaseName

/-- schema's `Lease` bucket, as the backend names it (`bucket{id: 3, name: "lease",
safeRangeBucket: false}`). -/
def leaseBI : backend.BucketInfo := ⟨W64 3, leaseName, false⟩

/-- **The backend's parameters let the lessor delete from `Lease`**: the bucket in the table, a
tracked one (`RB`, D22), none of its keys a hook's own (leases T3, 2026-10-25). -/
def leaseParams (P : backend.BParams) : Prop :=
  P.has leaseBI ∧ P.RB leaseName = true ∧ ∀ k, P.hk leaseName k = false

/-- The tracked buckets `r` (`backend.rbData`) after the key `k` of bucket `n` is deleted (the
bucket created empty if absent, as the backend's `UnsafeDelete` leaves it). -/
def rbDel (r : GMap GoString backend.BktData) (n k : GoString) : GMap GoString backend.BktData :=
  r.insert n (((r.lookup n).getD ∅).delete k)

/-- **What the batch transaction's lock token `U` allows, the session's puts being `l`**: only
`Unlock()`, as `batchTxSpecG`'s two (with no puts, the lock's resource `W` and the invariant `P`
back; else the bucket's whole view, written back). The token a `Lease` delete leaves
(`batchTxSpecG`'s last clause: leases T3, 2026-10-25). -/
def unlockAt (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W P : IProp GF) (U : IProp GF)
    (l : Puts) : IProp GF :=
  iprop(□ ({{ U ∗ ⌜l = []⌝ ∗ W ∗ P }} (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); True }}) ∗
    □ (∀ (m : Bucket) (Q : IProp GF),
      {{ U ∗ View 1 m ∗ (View 1 (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) -∗ W ∗ Q) ∗ P }}
        (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); Q }}))

/-- **A capability to put a compaction key into the `Meta` bucket** (the backend-compaction stage,
review round 2, R2-3): from the token `X`, `UnsafePut(schema.Meta, k, v)` at a compaction key
(`metaCompactKey`) of a value the store writes there (`metaRevVal`) leaves the token `Y`. The batch
transaction gives one from a fresh session's lock to a token only `Unlock` takes (`batchTxSpecG`'s
`Meta` clause: `SetScheduledCompact`'s session), and one per step of a compacting range's token
(the job's last batch: `UnsafeSetFinishedCompact`). The key and value slices are read-only for
good (`↦*□`): the backend's write buffer keeps them (`txWriteBuffer.put` stores the slices, not
copies; review round 6's finding: until then they were lent fractionally and given back, which no
buffering backend can meet); mvcc's callers never write them again (`UnsafeSet*Compact`'s
`rbytes`). -/
def metaPutCap (bt : GoInterfaceOk) (X : IProp GF) (Y : GoString → GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (b : GoInterface) (key val : GoSlice) (k v : GoString),
    ⌜metaCompactKey k ∧ metaRevVal v⌝ →
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ X ∗ key ↦*□ k ∗
        val ↦*□ v }}
      (App (App (App (Val #(methods bt.ty go!"UnsafePut" bt.v)) (Val #b)) (Val #key)) (Val #val))
    {{ RET #(); Y k v }})

/-- **The compaction keys' values after a put of `v` at the compaction key `k`** (the snapshot
image's (b), 2026-11-05): the finished key's or the scheduled key's value replaced
(`backend.fkVals`' pair: finished, scheduled). -/
def fkPutV (w : backend.FkVals) (k v : GoString) : backend.FkVals :=
  if k = finKeyBytes then (some v, w.2) else (w.1, some v)

/-- **The deleted entries after a compaction delete of the `Key` bucket's key `k`** (the snapshot
image's (b), 2026-11-05; `Api/SnapImage.lean`'s `cutAt_del`, `hX'`): `k` recorded, every other
`Key` entry's record unchanged. -/
def dlStep (X X' : backend.VData) (k : GoString) : Prop :=
  ∀ k', (X'.lookup (keyName, k')).isSome = ((X.lookup (keyName, k')).isSome || decide (k' = k))

/-- **The limited range's batch bound** (the backend-compaction stage, decision O3; review round 2,
R2-3): a compacting range reads at most `2^56` entries, so the session it ends (`limit` deletes and
one `Meta` put after a start below the backend's `P.limit ≤ 2^57`) stays within the backend's count
(`pend + hookMax < 2^58`). The job reads `CompactionBatchLimit` entries: the store's scope premise
(`isStore`'s `Hcfgl`; Go has no such bound). -/
abbrev rangeLimitMax : Int := 2 ^ 56

/-- **`LockInsideApply` with no hook set** (M2, the storage side, item 31; moved from `LockArm.lean`,
2026-10-30, as `batchTxSpecG`'s clause): from the session's tokens and the unset hook `HN`, the
lock, its resource `W` and the batch lock's invariant `P` itself (no hook ran). -/
def lockNilSpec (bt : GoInterfaceOk) (RT WT W P HN : IProp GF) (Locked : Puts → IProp GF) :
    IProp GF :=
  iprop(□ (∀ Pre : IProp GF,
    {{ Pre ∗ RT ∗ WT ∗ HN }} (App (Val #(methods bt.ty go!"LockInsideApply" bt.v)) (Val #()))
    {{ RET #(); Locked [] ∗ W ∗ P ∗ Pre ∗ RT ∗ HN }}))

/-- The batch transaction `bt` (`backend.BatchTx`, names-only: the trust boundary of the
backend's write path), as the write transaction uses it, with `Locked l` its lock's token
holding the puts `l` since the lock was taken, `RT` a client's token it is lent (the reader's
budget token of `isKeyBackendG`: the backend open while the lock is taken), `WT` a write
session's token (the backend's write-back budget: every `Unlock` may write back), and `PutOk` a
condition of the puts (the backend's bounds and order): `LockInsideApply()` takes the lock (no
puts yet), for a session's token, and gives the lock's resource `W` (what the store keeps under
it); `UnsafeSeqPut(schema.Key, k, v)` under it adds a put (its key and value slices read-only
for good: the backend's write buffer and bbolt keep them), for a put meeting the condition
`PutOk m l k v` over the bucket `m` the caller holds a view of (the real backend's: the key above
every key of the bucket and of the session's puts, 2026-10-13, unit 5); `Unlock()` takes the
resource back
and, with no puts, leaves the bucket as it is, else writes the puts back into the bucket, whose
view `View 1 m` the caller holds (`storeTxnWrite.End` holds it, half under `s.revMu`, half in
`W`), in order, then releases the lock with `W` made of the updated view (a wand: `W` holds part
of the view); `UnsafeRange(schema.Key, k, nil, 0)` under the lock reads the bucket the caller
holds a view of with the puts so far (the batch transaction sees its own puts), its slices
readable through some `Rd` under a token `T` the lock token is lent as until the next call (the
backend's `batchLocked` at the session's state, whose bbolt transaction the slices are of), but
for a key compaction may have deleted (`Del k`: no key and no value).

**Compaction** (2026-10-13, unit 5a; `notes/decisions.md`, "mvcc: compaction"; restated by the
backend-compaction stage, review rounds 1-2):
`LockOutsideApply()` with the deposit witness `Dep` (`batchTxInitSpec`'s first `Unlock` returns
it) gives `W` (the compaction job's lock, after `NewStore`). Where the backend supports mvcc's
compaction (`Cmp`): `UnsafeRange(schema.Key, lo, hi, limit)`, from a fresh session's lock
(`Locked []`) with `0 < limit ≤ rangeLimitMax`, reads the first `limit` entries in `[klo, khi)`, in
key order, of the bucket, some keys compaction may delete missing (`snapThin`), and ends the session
in a delete-only token `U (limit + 1)` (the lessor's `unlockAt` precedent): its slices are lent,
readable under any `U n` (`rdCap`/`rdCap2`: bbolt's slices die at the session's commit); a key it
returned that compaction may delete (`Del k`, the store's `delKey`) is deleted, and a compaction key
(`metaCompactKey`) put into `Meta` with a value the store writes there (`metaRevVal`), each from
`U (n + 1)` to `U n`, the view unchanged (the deletion shows only in what later reads may miss);
`Unlock` takes any `U n`. (The snapshot image's tracking, the job, 2026-11-06) The range, lent the
right `MW w0 X0`, reads every entry of the physical bucket (the view but the deleted entries `X0`
the backend records, `snap.physLookup`): what the job's cursor needs. A `Meta` put on its own (`metaPutCap`) goes from `Locked []` to such a
token. Every `Meta` put of a compaction key, the job's and the one on its own, also takes and gives
back the right `MW w X` to write them (`kbMWv`: the real backend's half of its compaction-key flag;
review rounds 8-9), at the compaction keys' values `w` and the deleted entries `X` the backend
records (the snapshot image's (b), 2026-11-05): a delete of a key the range read records it
(`dlStep`), a put moves the values (`fkPutV`). The store's record of the meta keys is its own
(`metaCompact`).

**The lessor's delete** (leases T3, 2026-10-25; `notes/leases-plan.md`): `lessor.Revoke` deletes
the lease's record from the `Lease` bucket under the lock of the KV write transaction its range
deleter opened (`UnsafeDelete(schema.Lease, k)`, the store's batch transaction's), with the right
`Rb r` to write the tracked buckets `r` (the real backend's client half of them, `rbOwn`; the
bucket is tracked, D22), given back as `Rb (rbDel r leaseName k)`. The lock's token becomes one
that only `Unlock` takes (`unlockAt`, at the same puts): the backend counts its pending
operations, and the store makes no other call after it (`Revoke` ends the transaction).

The store's instance over mvcc's assumed backend (`batchTxSpec`) has no tokens (`RT = WT =
True`), no condition and `Cmp`: the backend's bridge (`BackendBridge.lean`) proves the general
one with the backend's, `Cmp` false (2026-10-13, unit 4; the merge with the compaction).

**No hook set** (M2, the storage side, item 31, 2026-10-30): `LockInsideApply` with the unset hook
`HN` lent runs nothing (`lockNilSpec`: the lock, `W` and `P` itself). The real backend's `HN` is the
client's half of its hook variable at `nil` (`kbHookNil`, held until the server sets the hook:
`restore()`'s resumed compaction locks before); `False` (the default) where no caller can lend it. -/
def batchTxSpecG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF) (P : IProp GF)
    (HF : val → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (MW : backend.FkVals → backend.VData → IProp GF) (HN : DFrac → IProp GF := fun _ => iprop(False)) :
    IProp GF :=
  iprop(□ (∀ (Pre Q : IProp GF) (f : val),
      {{ Pre ∗ RT ∗ WT ∗ HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
        (App (Val #(methods bt.ty go!"LockInsideApply" bt.v)) (Val #()))
      {{ RET #(); Locked [] ∗ W ∗ Q ∗ RT }}) ∗
    □ (∀ (l : Puts) (q : Qp) (m : Bucket) (b : GoInterface) (key val : GoSlice) (k v : GoString),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked l ∗ View q m ∗
          key ↦*□ k ∗ val ↦*□ v ∗ ⌜PutOk m l k v⌝ }}
        (App (App (App (Val #(methods bt.ty go!"UnsafeSeqPut" bt.v)) (Val #b)) (Val #key))
          (Val #val))
      {{ RET #(); Locked (l ++ [(k, v)]) ∗ View q m }}) ∗
    □ ({{ Locked [] ∗ W ∗ P }} (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); True }}) ∗
    □ (∀ (l : Puts) (m : Bucket) (Q : IProp GF),
      {{ Locked l ∗ View 1 m ∗ (View 1 (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) -∗ W ∗ Q) ∗
          P }}
        (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); Q }}) ∗
    □ (∀ (l : Puts) (q : Qp) (m : Bucket) (b : GoInterface) (key : GoSlice) (k : GoString)
        (dq : DFrac),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked l ∗ View q m ∗
          key ↦*{dq} k }}
        (App (App (App (App (Val #(methods bt.ty go!"UnsafeRange" bt.v)) (Val #b)) (Val #key))
          (Val #(slice.nil))) (Val #(W64 0)))
      {{ (ks vs : GoSlice), RET (PairV #ks #vs); ∃ (Rd : GoSlice → GoString → IProp GF)
          (T : IProp GF), T ∗ (T -∗ Locked l) ∗ rdCap Rd T ∗ View q m ∗ key ↦*{dq} k ∗
          (keyVals Rd ks vs (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) k ∨
            (Del k ∗ ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice))) }}) ∗
    □ ({{ Dep ∗ RT ∗ WT }} (App (Val #(methods bt.ty go!"LockOutsideApply" bt.v)) (Val #()))
      {{ RET #(); Locked [] ∗ W ∗ P ∗ RT }}) ∗
    -- (the backend-compaction stage, review round 2, R2-3; the lessor's `unlockAt` precedent) the
    -- limited range, from a fresh session's lock, ends the session in a token `U` that counts what
    -- is left of the call's budget: its slices are readable under any `U n` (lent: bbolt's slices
    -- die at the session's commit), a key it returned is deleted and a compaction key put into
    -- `Meta` from `U (n + 1)` to `U n`, and `Unlock` takes any `U n`; no put or second range after
    -- it (the job makes neither), so the backend's count stays local to the call
    □ (⌜Cmp⌝ -∗ ∀ (q : Qp) (m : Bucket) (b : GoInterface) (lo hi : GoSlice)
        (klo khi : GoString) (limit : w64) (dqlo dqhi : DFrac) (w0 : backend.FkVals)
        (X0 : backend.VData),
      ⌜0 < sint.Z limit ∧ sint.Z limit ≤ rangeLimitMax ∧ khi ≠ []⌝ →
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked [] ∗ View q m ∗
          lo ↦*{dqlo} klo ∗ hi ↦*{dqhi} khi ∗ MW w0 X0 }}
        (App (App (App (App (Val #(methods bt.ty go!"UnsafeRange" bt.v)) (Val #b)) (Val #lo))
          (Val #hi)) (Val #limit))
      {{ (ks vs : GoSlice), RET (PairV #ks #vs); View q m ∗ lo ↦*{dqlo} klo ∗
          hi ↦*{dqhi} khi ∗ MW w0 X0 ∗
          ∃ (m' : Bucket) (Rd : GoSlice → GoString → IProp GF) (U : Nat → IProp GF),
            U ((sint.Z limit).toNat + 1) ∗
            snapThin m m' Del ∗
            ⌜∀ k, snap.physLookup m X0 k ≠ none → (m'.lookup k).isSome⌝ ∗
            (□ ∀ n : Nat, rdCap Rd (U n)) ∗ (□ ∀ n : Nat, rdCap2 Rd (U n)) ∗
            pairVals Rd ks vs ((bucketRange m' klo khi).take (sint.Z limit).toNat) ∗
            □ (∀ (key : GoSlice) (k : GoString) (n : Nat),
              ∀ (w : backend.FkVals) (X : backend.VData),
              {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ U (n + 1) ∗
                  Del k ∗ □ Rd key k ∗ ⌜(m'.lookup k).isSome⌝ ∗ MW w X }}
                (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key))
              {{ RET #(); U n ∗ ∃ X' : backend.VData, MW w X' ∗ ⌜dlStep X X' k⌝ }}) ∗
            (□ ∀ (n : Nat) (w : backend.FkVals) (X : backend.VData),
              metaPutCap bt iprop(U (n + 1) ∗ MW w X) (fun k v => iprop(U n ∗ MW (fkPutV w k v) X))) ∗
            □ (∀ n : Nat, {{ U n ∗ W ∗ P }} (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
                {{ RET #(); True }}) }}) ∗
    -- (R2-3) a compaction key put into `Meta` in a fresh session (`SetScheduledCompact`'s) ends
    -- it in a token only `Unlock` takes, as the lessor's delete does; with the right `MW` to write
    -- the compaction keys, given back (the real backend's client half of its compaction-key flag,
    -- `backend.fkOwn`: the backend-compaction stage, 2026-10-29; `True` for mvcc's assumed backend)
    □ (⌜Cmp⌝ -∗ ∀ (w : backend.FkVals) (X : backend.VData), metaPutCap bt iprop(Locked [] ∗ MW w X)
      (fun k v => iprop((∃ U : IProp GF, U ∗ unlockAt bt View W P U []) ∗ MW (fkPutV w k v) X))) ∗
    □ (∀ (l : Puts) (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac)
        (r : GMap GoString backend.BktData),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b ∗ Locked l ∗
          key ↦*{dq} k ∗ Rb r }}
        (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key))
      {{ RET #(); (∃ U : IProp GF, U ∗ unlockAt bt View W P U l) ∗ key ↦*{dq} k ∗
          Rb (rbDel r leaseName k) }}) ∗
    -- (M2, item 31) `LockInsideApply` with no hook set, the unset hook `HN dq` lent (§4.8, 2026-11-06:
    -- at any share `dq` of it, the frozen one `DFrac.discard` of a store without a hook among them)
    □ (∀ dq : DFrac, lockNilSpec bt RT WT W P (HN dq) Locked))

/-- `NewStore`'s calls on a fresh backend's batch transaction `bt`, with `LockedO n` the lock's
token after `n` buckets created: `LockOutsideApply()` takes the lock, for a session's token
`WT` (the client's token `RT` lent), with the lock's initial resource `Wi` only (`True` for
mvcc's assumed backend; the real backend's late-bound resource `lateW`, not yet registered,
2026-10-13, unit 5): the backend's batch lock holds `W` from `NewStore`'s first `Unlock()` on
(the triple takes `W` and deposits it there, returning the deposit witness `Dep`, persistent,
which the compaction job's `LockOutsideApply` needs: `True` of the real backend, whose lock
holds the late-bound `W` from its creation; `NewStore` builds `W` before, from `Wi`);
`LockInsideApply` is the writers' lock, taken after that. `UnsafeCreateBucket(b)`
under the lock, of schema's `Key` or `Meta` bucket, creates it (not touching the `Key` bucket's
entries), at most twice (the backend's bound on a session's operations; `NewStore` creates
two). -/
def batchTxInitSpec (bt : GoInterfaceOk) (RT WT : IProp GF) (W Wi Dep : IProp GF)
    (LockedO : Nat → IProp GF) (P : IProp GF) : IProp GF :=
  iprop(□ ({{ RT ∗ WT }} (App (Val #(methods bt.ty go!"LockOutsideApply" bt.v)) (Val #()))
      {{ RET #(); LockedO 0 ∗ Wi ∗ P ∗ RT }}) ∗
    □ (∀ (n : Nat) (b : GoInterface),
      {{ LockedO n ∗ ⌜n < 2⌝ ∗ (globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∨
          globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b) }}
        (App (Val #(methods bt.ty go!"UnsafeCreateBucket" bt.v)) (Val #b))
      {{ RET #(); LockedO (n + 1) }}) ∗
    □ (∀ n : Nat,
      {{ LockedO n ∗ W ∗ P }} (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); □ Dep }}))

/-- `bt` is a batch transaction (its lock tokens' predicates are its own). -/
def isBatchTxG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (Bt : GoInterfaceOk → IProp GF := fun _ => iprop(True)) (MW : backend.FkVals → backend.VData → IProp GF)
    (HN : DFrac → IProp GF := fun _ => iprop(False)) :
    IProp GF :=
  iprop(∃ (Locked : Puts → IProp GF) (LockedO : Nat → IProp GF),
    batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW HN ∗
      batchTxInitSpec bt RT WT W Wi Dep LockedO P ∗ □ Bt bt)

/-- No condition on the puts (mvcc's assumed backend). -/
def noPutCond : Bucket → Puts → GoString → GoString → Prop := fun _ _ _ _ => True

/-- **The real backend's condition on a put** (`BackendBridge.lean`): at most `2^56` puts in a
session (the backend's bound on a session's operations), a key of `1..MaxKeySize` bytes above
every key of the bucket `m` and of the session's puts `l` (the safe-range discipline of the
`Key` bucket, and `UnsafeSeqPut`'s order check). (No bound on the value: bbolt refuses one above
`MaxValueSize` and the backend's `lg.Fatal` exits:
`nonissues/etcd-backend-put-value-too-large-fatal.md`.) -/
def keyPutOk (m : Bucket) (l : Puts) (k _v : GoString) : Prop :=
  l.length < 2 ^ 56 ∧ 0 < k.length ∧ k.length ≤ backend.maxKeySize ∧
    (∀ k' v', m.lookup k' = some v' → go.GoStringLt k' k) ∧ ∀ p ∈ l, go.GoStringLt p.1 k

/-- `b` is a `Backend` whose `ConcurrentReadTx()` and `ReadTx()`, for a reader's token `RT`
(the backend's readers are bounded: a slot of its read lock and of its `txMu`, a budget token,
and the backend open; given back by the reader's `RUnlock`), return a snapshot reader of the
bucket the caller holds as `View q m` (any fraction `q`), which the caller keeps, with the right
`L` to lock it (`keyReadSnap`: its `RLock` gives the reader's token, its `RUnlock` takes it),
and whose `BatchTx()` is a batch transaction over the view, its lock holding `W`;
`ForceCommit()`, for a session's token `WT` (`RT` lent), returns (the commit to disk has no
effect on the view), serving a request `X ⇒ Y` the backend serves (`Req`: by default a plain wand;
the real backend's, `bkReq`: its hooks', D22 the stored-index window, 2026-10-23); `Size()`/`SizeInUse()` return some number. The snapshots may miss keys
compaction may have deleted (`Del`, `snapThin`), and the batch transaction's lock, after
`NewStore`'s first `Unlock`, holds `W` with the deposit witness `Dep` (persistent, its own).
Where the backend supports mvcc's compaction (`Cmp`): the job's calls, with no effect on the
model, `LockForSafeRangeDelete()`/`UnlockForSafeRangeDelete()` (the defragmentation's exclusion)
and `ReadTx()` with no view, for the reads of the `Meta` bucket's compaction keys alone
(`metaReadTx`: `checkPrevCompactionCompleted`; its `RLock` takes the reader's token `RT`, which
its `RUnlock` gives back). Under `NC` (the backend records no compaction:
`kbNoCmp`) a `ReadTx` reader's reads of those keys find nothing (`keyReadLocked`); their writes, in
the batch transaction's `Cmp` clauses, need the right `MW` at its values (`kbMWv`: the real
backend's half of its compaction-key flag with its halves of the values, `bkMW`). The instance of mvcc's assumed backend
(`isKeyBackend`) has no tokens, no condition on the puts (`batchTxSpecG`'s `PutOk`) and `Cmp`;
`BackendBridge.lean` proves the general one of the backend, `Cmp` false (2026-10-13, unit 4; the
merge with the compaction, unit 5a). -/
def isKeyBackendG (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF := fun X Y => iprop(□ (X -∗ Y)))
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (Bt : GoInterfaceOk → IProp GF := fun _ => iprop(True))
    (SR SRh : IProp GF := iprop(True)) (MW : backend.FkVals → backend.VData → IProp GF) (HN : DFrac → IProp GF := fun _ => iprop(False)) :
    IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnap View RT NC Del false rt m L }}) ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnap View RT NC Del true rt m L }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt);
          isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW HN }}) ∗
    □ (∀ (X Y : IProp GF),
      {{ RT ∗ WT ∗ X ∗ Req X Y }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      {{ RET #(); RT ∗ Y }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"Size" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"SizeInUse" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ (⌜Cmp⌝ -∗
      □ ({{ SR }} (App (Val #(methods bi.ty go!"LockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); SRh }}) ∗
      □ ({{ SRh }} (App (Val #(methods bi.ty go!"UnlockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); SR }}) ∗
      □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); metaReadTx rt RT }})))

/-! ## The lessor

(2026-10-13, unit 8 of the backend: the lessor's KV-facing methods are proved,
`Proof/go_etcd_io/etcd/server/v3/lease/`; this contract is derived from them,
`lease.isLessor_of_lessorInv`.) A lease is live for the holder of the lease owner's half of the
lessor's live set (`lease.leaseOwn γl L`: `L`), not for good: `Revoke` shrinks `L`, after which
`Attach` returns `ErrLeaseNotFound` (on which mvcc's `put` panics). So `Attach` takes the
owner's half and the lease's membership, and `GetLease` a reader slot of the lessor's lock
(`lease.lessorRd`; the store keeps one, `lessorRdOf` in its writer's resource). (Unit T3, L2b,
2026-10-25) The owner's resource also holds the item map `I` (`lease.leaseOwn γl L I`), which
the three calls read and change: so the store's caller, holding it, knows each key's lease. -/

/-- The lessor `le` (the real `*lessor` at `lp`, ghost map `γl`), as the KV core uses it:
`GetLease(item)` returns the owner's item map's lease of `item` (`NoLease` if none), with a
reader slot; `Attach(id, items)` of a live lease (`id ∈ L`) of items on no other lease adds them
to the item map and returns `nil`; `Detach(id, items)` of items the item map puts on `id` removes
them and returns `nil`. The items are read. `SetRangeDeleter(f)`
sets the deleter, by its owner (`lease.rdOwn γl`, unit T3): `NewStore` passes the closure
`func() lease.TxnDelete { return s.Write(traceutil.TODO()) }` (the store's own verified
`store.Write`), `newWatchableStore` the watchable store's. The lessor's ghost name `γl` is its
own (it exists before the store). -/
def isLessor (le : GoInterface) (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, ⌜le = lease.lessorIface lp⌝ ∗ lease.lessorPin γl lp ∗
    □ (∀ (item : go_etcd_io.etcd.server.v3.lease.LeaseItem) (L : List w64)
        (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ lease.lessorRd lp γl ∗ lease.leaseOwn γl L I }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"GetLease" #lp)) (Val #item))
      {{ RET #((I.lookup item).getD (W64 0)); lease.lessorRd lp γl ∗ lease.leaseOwn γl L I }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ lease.leaseOwn γl L I ∗ ⌜id ∈ L⌝ ∗
          ⌜∀ it ∈ l, I.lookup it = none ∨ I.lookup it = some id⌝ ∗
          ⌜∀ it ∈ l, (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗ items ↦*{dq} l }}
        (App (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"Attach" #lp)) (Val #id)) (Val #items))
      {{ RET #(GoInterface.nil); lease.leaseOwn γl L (lease.insertAll I l id) ∗ items ↦*{dq} l }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ lease.leaseOwn γl L I ∗ ⌜l ≠ []⌝ ∗ ⌜∀ it ∈ l, I.lookup it = some id⌝ ∗ items ↦*{dq} l }}
        (App (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"Detach" #lp)) (Val #id)) (Val #items))
      {{ RET #(GoInterface.nil); lease.leaseOwn γl L (lease.deleteAll I l) ∗ items ↦*{dq} l }}) ∗
    □ (∀ (f0 f : GoFunc),
      {{ lease.rdOwn γl f0 }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"SetRangeDeleter" #lp)) (Val #f))
      {{ RET #(); lease.rdOwn γl f }}))

/-! ## The backend instances (2026-10-13, unit 5)

The store is over one of two backends, named by its `StoreNames.kb`: mvcc's assumed contract
(`none`: the view is the store's own ghost map, no tokens, no condition on the puts, `W` the
writer's resource itself) or the real backend (`some d`: the backend's clients' view of the `Key`
bucket, a reader's slot of the backend and a share of it open, a write-back's budget, the
safe-range condition on the puts, and the batch lock's late-bound resource `lateW`). -/

/-- The readers' view `vd` of the backend is the `Key` bucket `m`, and nothing else. -/
def keyView (vd : backend.VData) (m : Bucket) : Prop :=
  ∀ n k, vd.lookup (n, k) = if n = keyName then m.lookup k else none

/-- mvcc's view of the `Key` bucket over the real backend, at fraction `q`: the backend's
clients' view (`bView`) of it. -/
def bkView (γB : backend.BNames) (q : Qp) (m : Bucket) : IProp GF :=
  iprop(∃ vd : backend.VData, backend.bView γB q vd ∗ ⌜keyView vd m⌝)

/-- The view of the bucket in the instance `kb` (`γb` the store's ghost map, for `none`). -/
def kbView (kb : Option KBReal) (γb : GName) (q : Qp) (m : Bucket) : IProp GF :=
  match kb with
  | none => ghostMapAuth γb q m
  | some d => bkView d.γB q m

/-- A reader's token in the instance `kb`: for the real backend, a reader's slot of it and the
reader's share `rdOpen` of it open (given back at the reader's `RUnlock`; D22 receiver epochs, S8d,
W7, 2026-10-25: a fixed share, until then some share). -/
def kbRT (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => iprop(backend.rdTok d.γB d.P d.be ∗ backend.bOpen d.γB backend.rdOpen)

/-- A write session's token in the instance `kb`: for the real backend, a write-back's budget
(every `Unlock` may increment the read buffer's version, a `uint64`: `backend.wbTok`). -/
def kbWT (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => backend.wbTok d.γB

/-- **The safe-range deletion's slot** in the instance `kb` (the backend-compaction stage,
`notes/backend-cmp-plan.md` 3.4, 2026-10-28): for the real backend, a reader's slot of its
`safeRangeDeleteMu` (which the compaction job's `LockForSafeRangeDelete` read-locks; the
defragmentation, out of scope, is its only writer). -/
def kbSR (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => backend.srSlot d.be

/-- **The safe-range deletion's slot, read-locked** in the instance `kb` (the contract's `SRh`;
question 5's core stage, parts (2)-(4)): for the real backend, its `safeRangeDeleteMu` read-locked
(`backend.srHeld`, between the compaction job's `LockForSafeRangeDelete` and its deferred
`UnlockForSafeRangeDelete`); nothing for mvcc's assumed backend. -/
def kbSRh (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => backend.srHeld d.be

/-- **The compaction mode of the instance** (question 5, Q5-1, the user's: the mode lives in the
instance): the real backend supports mvcc's compaction when its creator chose it (`KBReal.cm`, M2's
`ρ.kv.cmp`; `false` for D22's received backends, "no restore in compaction mode"); mvcc's assumed
backend always. What gates the compaction's resources below; `kbCmp` is it since the core
stage's flip (`notes/backend-cmp-plan.md`, "Question 5's switch"). -/
def kbCmpM (kb : Option KBReal) : Prop :=
  match kb with
  | none => True
  | some d => d.cm = true

instance kbCmpM_dec (kb : Option KBReal) : Decidable (kbCmpM kb) := by
  unfold kbCmpM; cases kb <;> infer_instance

/-- **The real backend's commit requests** (D22 the stored-index window, 2026-10-23): a plain wand,
or a request its hooks serve (`backend.commitReq`) for some batch-lock and hooks' resources of
the backend. -/
def bkReq (γB : backend.BNames) (P : backend.BParams) (b : Loc) (X Y : IProp GF) : IProp GF :=
  iprop(□ (X -∗ Y) ∨ ∃ W Pk : IProp GF, backend.isBackend γB P W Pk b ∗
    backend.commitReq γB P Pk b X Y)

/-- The commit requests `ForceCommit` serves in the instance `kb`: mvcc's assumed backend's
are plain wands; the real backend's, `bkReq`. -/
def kbReq (kb : Option KBReal) : IProp GF → IProp GF → IProp GF :=
  match kb with
  | none => fun X Y => iprop(□ (X -∗ Y))
  | some d => bkReq d.γB d.P d.be

/-- The condition on a put in the instance `kb`. -/
def kbPutOk (kb : Option KBReal) : Bucket → Puts → GoString → GoString → Prop :=
  match kb with
  | none => noPutCond
  | some _ => keyPutOk

/-- The store's view of the bucket (`kbView` of its instance). -/
def bucketView (γ : StoreNames) (q : Qp) (m : Bucket) : IProp GF := kbView γ.kb γ.bucket q m

/-- The store's reader token (`kbRT`). -/
abbrev storeRT (γ : StoreNames) : IProp GF := kbRT γ.kb

/-- The store's write token (`kbWT`): `store.Write` spends one. -/
abbrev storeWT (γ : StoreNames) : IProp GF := kbWT γ.kb

/-- The store's backend's commit requests (`kbReq`). -/
abbrev storeReq (γ : StoreNames) : IProp GF → IProp GF → IProp GF := kbReq γ.kb

/-- The store's condition on its backend's puts (`kbPutOk`). -/
abbrev storePutOk (γ : StoreNames) : Bucket → Puts → GoString → GoString → Prop := kbPutOk γ.kb

/-- Whether the backend of the instance `kb` supports mvcc's compaction (`isKeyBackendG`'s
`Cmp`): its compaction mode (`kbCmpM`; question 5's core stage, part (4), the flip, 2026-10-29:
until then `kb = none`, mvcc's assumed backend only). mvcc's assumed backend always does; the real
backend when its creator chose it (`KBReal.cm`, Q5-1, the user's), its contract then from the new
bridge (`isKeyBackendG_of_backendC` at `Cmp := True`, the deletable keys the store's through the
backend's registration: `storeBackendT_of_backendC`); a real store that does not compact keeps the
old bridge (`storeBackendT_of_backend`, `dlNoDel`). -/
def kbCmp (kb : Option KBReal) : Prop := kbCmpM kb

/-- The store's backend supports compaction (`kbCmp`). -/
abbrev storeCmp (γ : StoreNames) : Prop := kbCmp γ.kb

/-- **The right to write the tracked buckets** (`batchTxSpecG`'s `Rb`, at the buckets `r`) of the
instance `kb`: the real backend's client part of the `Lease` bucket (`backend.rbPart`, D22), with
its parameters letting the lessor delete from `Lease` (`leaseParams`: the holder knows the table);
nothing for mvcc's assumed backend (leases T3, 2026-10-25: what the lessor's delete in `Revoke`
takes). (2026-11-02, the backend-auth-split stage: until then the whole client half `rbOwn`; the
revocation's delete writes `Lease` only, and the server's rest resource holds the cluster's buckets
idle, which the whole half could not give back.) -/
def kbRb : Option KBReal → GMap GoString backend.BktData → IProp GF
  | none => fun _ => iprop(True)
  | some d => fun r => iprop(backend.rbPart d.γB (· = leaseName) r ∗ ⌜leaseParams d.P⌝)

/-- The store's right to write the tracked buckets (`kbRb`). -/
abbrev storeRb (γ : StoreNames) : GMap GoString backend.BktData → IProp GF := kbRb γ.kb

/-- **The real backend at `be` has the batch transaction `bt`** (persistent): its `batchTx`
field, read-only, holds `bt`'s pointer, and `BatchTx()` returns the field's value (so a call
returns `bt`: the field's points-to agree). -/
def bkBt (be : Loc) (bt : GoInterfaceOk) : IProp GF :=
  iprop(∃ t : Loc, ⌜bt = ⟨go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty, #t⟩⌝ ∗
    backend.bF go!"batchTx" be ↦□ t ∗
    □ ({{ True }}
      (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        go!"BatchTx" #be)) (Val #()))
      {{ (t' : Loc), RET #(interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty) #t');
        backend.bF go!"batchTx" be ↦□ t' }}))

/-- **The batch transaction `bt` is the backend's** (`isKeyBackendG`'s `Bt`; leases T3, L2d (iv),
2026-10-25) for the instance `kb`: over the real backend at `d.be`, its `BatchTx()` returns `bt`
(the backend's `batchTx` field, read-only), so that the lessor's `le.b.BatchTx()` in `Revoke` is
the batch transaction the KV write transaction holds the lock of; nothing over mvcc's assumed
backend. -/
def kbBt : Option KBReal → GoInterfaceOk → IProp GF
  | none => fun _ => iprop(True)
  | some d => bkBt d.be

/-- The store's batch transaction is its backend's (`kbBt`). -/
abbrev storeBt (γ : StoreNames) : GoInterfaceOk → IProp GF := kbBt γ.kb

/-- A revision token: the right to open one write transaction (`store.Write`). The store's
`NewStore` hands out `2 ^ 63 - 5` of them: with the budget `writerRes` keeps, the revision
counter stays below `2 ^ 63 - 2`. -/
def revToken (γ : StoreNames) : IProp GF := ownToks γ.revs 1

/-! ## Compaction: its revision, what it may delete, the meta keys -/

/- (Step 1's compaction right `compactRight γ c`, with the never-stopped scheduler `schedLive`, is
replaced by the restorable `compactRightR s γ c`, `InvCompact.lean`: M2, the storage side, the
approval's item 17, 2026-10-30.) -/

/-- The invariant's name of a frozen compaction revision. -/
abbrev crevFrozenN : Namespace := (nroot .@ "mvcc") .@ "crevFrozen"

/-- **No compaction, ever** (persistent): the compaction right at `-1`, given up into an
invariant (its half of the revision's authority; the jobs' queue dropped), so the revision stays
`-1` (no one can gather the authority
to update it). The store's readers and writers as the txn, apply, request path and watchable
store use them (`storeReader`, and the transactions at their defaults: `isTxnRead`, …) carry it:
their statements are of a store that is not compacted (the frozen corollaries, `spec_frozen`, of
the store's general specs; 2026-10-13, unit 6a). -/
def crevFrozen (γ : StoreNames) : IProp GF := inv crevFrozenN (crevUB γ.idx (1 : Qp).half (-1))

/-- **A certified compaction revision** (persistent; 2026-10-13, unit 6a): a certified log with
revision `c`. `s.mu`'s resource keeps it for the current compaction revision (`muInvAt`). Until
M2's item 18 (2026-10-30) it also said that revision `c` does not delete a key and put it again
(`NoDelPutAt`, which the one who compacts asserted); the fixed `doCompact` (etcd-io/etcd#22377)
needs no such premise. Trivial at `c < 0` (`crevSafe_neg`). -/
def crevSafe (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(∃ log : Log, idxCert γ.idx log ∗ ⌜c < log.length⌝)

/-- **The store's compaction permit is `Perm`** (C3's store law, 2026-11-02; persistent): a
predicate fixed when the store is created (`NewStore`), which every compaction revision the store
holds satisfies (`crevPermAt`). -/
def crevPermIs (γ : StoreNames) (Perm : Int → IProp GF) : IProp GF :=
  savedPredOwn γ.cperm DFrac.discard (fun c => iprop(□ Perm c))

/-- **The compaction revision `c` is permitted** (C3's store law; persistent): none yet (`-1`), or
the store's permit holds of it. `s.mu`'s and `s.revMu`'s resources keep it of their `c`
(`muInvAt`, `revMuBody`); `store.Compact` takes it of its revision. -/
def crevPermAt (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(⌜c = -1⌝ ∨ ∃ Perm : Int → IProp GF, crevPermIs γ Perm ∗ □ Perm c)

/-- **A key compaction may delete** (persistent, the store's choice of the backend contract's
`Del`): of a certified log, a revision's bytes compaction at a lower bound `c` of the
compaction revision may delete (`KeyDel`, `Compact.lean`): a read at or above the compaction
revision never names one (`rangeAnswers_not_del`; until M2's item 18, 2026-10-30, also with revision
`c` of the log not deleting then putting a key, `NoDelPutAt`, the compactor's assertion). -/
def delKey (γ : StoreNames) (k : GoString) : IProp GF :=
  iprop(∃ (c : Int) (log : Log), crevLb γ.idx c ∗ idxCert γ.idx log ∗
    ⌜-1 ≤ c ∧ KeyDel log c k⌝)

/-- **The frozen fact, by the mode** (M2, the storage side: P3, review rounds 1-3; a conjunct of
`isWatchableStore`): a store that does not compact (`γs.cm = false`: today's servers) is frozen
(`crevFrozen`); a compacting one is not. The mode is the logical one (`StoreNames.cm`, item 26:
`withPhys` keeps it, so a restore does not move it). A store over mvcc's assumed backend
(`kb = none`) counts as compacting (`kbCmpM none`, so `cm = true`): its creator gets the
authority's half (`crevRightM`) and chooses, by `noCompactor_of_new`, to freeze it and watch. -/
def wsFrozenM (γs : StoreNames) : IProp GF :=
  if γs.cm then iprop(True) else crevFrozen γs

/-- **The meta keys' record** at fraction `q`: the values the store last wrote at
`scheduledCompactRev` and `finishedCompactRev` (`none`: never), its own view of the `Meta`
bucket's compaction keys (not `MetaCI`, the consistent index's). The batch lock holds it. -/
def metaCompact (γ : StoreNames) (q : Qp) (sched fin : Option w64) : IProp GF :=
  ghostVar γ.cmeta q (sched, fin)

/-- A finished compaction's revision as an integer (`-1`: none). -/
def finRev : Option w64 → Int
  | some x => sint.Z x
  | none => -1

/-- **The write right's lock key** (question 5's core stage, part (1); the Draft's `mwKeyW`, review
round 15's N1): the batch lock's half of a boolean ghost variable `γmk` recording where the compaction
keys' write right is, at `true` (the right in the write right's invariant, `mwInv`) while the lock is
free. -/
def mwKey (γmk : GName) : IProp GF := ghostVar γmk (1 : Qp).half true

/-- **The key's slot in the batch lock's resource** (the Draft's `mwSlotW`; decided by the agent: in
the compaction's part `compactRes`, which every writer carries whole): the key when the store
compacts (`kbCmpM`), else nothing. -/
def mwSlot (γ : StoreNames) : IProp GF :=
  if kbCmpM γ.kb then mwKey γ.mwk else iprop(True)

/-- **The tracked compaction of a compacting real backend** (the snapshot image's (a), 2026-11-05;
`notes/mvcc-api-invariants.md`, "the snapshot image"): mvcc's halves of the compaction keys' values,
at the records' bytes, and of the deleted entries (`backend.fkdOwn`, `backend.dlsOwn`: the client's
halves, which a backend snapshot's observation compares with the batch lock's), half the records'
compaction revision (`rcvW`, the other half the writer's slot's), and the cut (`snap.cmpOk`) of the
physical `Key` bucket at the log `L` and the logical view `m`; nothing for any other backend. -/
def cmpTrack (γ : StoreNames) (L : Log) (m : Bucket) (rc : CmpRecs) : IProp GF :=
  match γ.kb with
  | some d => if d.cm = true then
      iprop(backend.fkdOwn d.γB (recBytes rc.fin, recBytes rc.sched) ∗
        ghostVar γ.rcv (1 : Qp).half rc.crev ∗ monoNatAuthOwn γ.rcl 1 (crevN rc.crev) ∗
        ∃ (X : backend.VData) (jc : Int × Rev), backend.dlsOwn d.γB X ∗
          ghostVar γ.jc (1 : Qp).half jc ∗ ⌜snap.cmpOk L m X rc jc⌝)
    else iprop(True)
  | none => iprop(True)

/-- The compaction's part of the batch lock's resource (at the batch lock's log `L`): the meta keys' record and the finished
compactions' counter, at or above the record's finished revision (the highest revision a job
finished at: the jobs run in the order of their revisions, but the batch lock's resource does not
know it, so a job finishing writes its revision and raises the counter to it, if below;
2026-10-13, unit 5c, contract correction: the counter was the record's revision exactly), and the
write right's key (`mwSlot`: question 5's core stage, part (1)); (the snapshot image's (a),
2026-11-05) an eighth of the bucket's view, at the logical view `m`, and the tracked compaction at
`L` and `m` (`cmpTrack`). -/
def compactRes (γ : StoreNames) (L : Log) : IProp GF :=
  iprop(∃ (sched fin : Option w64) (n : Nat) (m : Bucket), metaCompact γ 1 sched fin ∗
    monoNatAuthOwn γ.fin 1 n ∗ ⌜crevN (finRev fin) ≤ n⌝ ∗ mwSlot γ ∗
    bucketView γ (1 : Qp).half.half.half m ∗ cmpTrack γ L m ⟨fin, sched⟩)

/-! ## The locks -/

/-! ## The locks -/

/-- **The batch lock's key** (exclusive; D22 receiver epochs, S2, 2026-10-22): in the batch lock's
resource (`writerRes`), deposited by a writer holding the lock while it holds the writer's state
(`writerInv`): so a writer finds that state in the invariant. -/
def writerKey (γ : StoreNames) : IProp GF := ghostVar γ.wk 1 ()

/-- **A reader's part of `s.mu`'s deposit ghost** (D22 receiver epochs, S2): `s.mu`'s resource
holds the ghost at its fraction (`muInv`), so a holder of `s.mu` shared has this part: a read
transaction keeps it with its reader (`txReader`), a writer deposits it in the writer's invariant
while it holds the writer's state (`writerInv`), so the holder of `s.mu` exclusively (all of the
ghost) finds that state there. -/
def wDep (γ : StoreNames) : IProp GF := ghostVar γ.wr sync.rfrac.half ()

/-- **The bucket `m` the store's view holds, of the log `L`** (persistent; M2's item 15,
2026-11-02, `notes/decisions.md`, "The writer's relation thin"): `m` is `bucketMap L` but for keys
compaction may delete (`snapThin … (delKey γ)`), and `bucketMap L` itself when the store does not
compact. A restore in compaction mode installs a bucket thinned at the image's compaction revision
(`restoreImageM`); compaction itself deletes only physically (the backend's logical view stays
whole). -/
def bucketLog (γ : StoreNames) (L : Log) (m : Bucket) : IProp GF :=
  iprop(snapThin (bucketMap L) m (delKey γ) ∗ ⌜¬ kbCmpM γ.kb → m = bucketMap L⌝)

/-- **The store's part `q` of the bucket's view, of the log `L`** (M2's item 15): a view at a
bucket of `L` (`bucketLog`). What the writer's pieces (`writerRes`, `writerPin`, the write
transaction) and `s.revMu`'s resource hold. -/
def bucketViewL (γ : StoreNames) (q : Qp) (L : Log) : IProp GF :=
  iprop(∃ m, bucketView γ q m ∗ bucketLog γ L m)

/-- **The writer's pin's view the store keeps in its batch lock's resource** (track A, request 3,
2026-11-06; for a watchable store too since the watchable lock holds the whole notified log,
2026-11-06): a quarter of the bucket's view at the log. -/
def wrPin (γ : StoreNames) (L : Log) : IProp GF := bucketViewL γ (1 : Qp).half.half L

/-- The batch lock's resource for the store (`W` of `isKeyBackend`; physical, per backend: D22
receiver epochs, S2, 2026-10-22, until then also the writer's state, now `writerL`): the batch
lock's key, half the ghost of the log `L` the bucket's view is of (the other half is the
writer's state's, so the writer's log is the view's), an eighth of the bucket's view at `L` (another eighth
in the compaction's part, the writer's pin a quarter, `writerPin`; the other half under `s.revMu`:
the write transaction's reads of the bucket, through the batch transaction),
the certificate of `L`, and the compaction's part (`compactRes`: the meta keys' record, the
finished compactions' counter). -/
def writerRes (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ L : Log,
    "Hwk" ∷ writerKey γ ∗
    "Hwv" ∷ ghostVar γ.wv (1 : Qp).half L ∗
    "Hbv" ∷ bucketViewL γ (1 : Qp).half.half.half L ∗
    "#Hcert" ∷ idxCert γ.idx L ∗
    "%Hne" ∷ ⌜L ≠ []⌝ ∗
    "Hcres" ∷ compactRes γ L ∗
    "Hpin" ∷ wrPin γ L)

/-- **The backend of the instance `kb` has nothing deletable** (persistent): for the real
backend, its creator fixed its deletable keys at none (`backend.dlNoDel`: a store that does not
compact). -/
def kbNoDel (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => backend.dlNoDel d.γB

/-- **The writer's loan of a store that does not compact**: its backend's no-compaction token
(`kbNoCmp`, the client's half of the compaction-key flag at `0`) and its nothing-deletable fact
(`kbNoDel`); nothing for a compacting store (its token is in `mwInv`). -/
def writerLoan (γ : StoreNames) : IProp GF :=
  if kbCmpM γ.kb then iprop(True) else iprop(kbNoCmp γ.kb γ.bucket ∗ kbNoDel γ.kb)

/-- **A write transaction's part of the bucket's view** (the snapshot image's (a), 2026-11-05):
the writer's pin's quarter and `writerRes`'s eighth (the compaction's part keeps its own eighth). -/
abbrev txQ : Qp := (1 : Qp).half.half + (1 : Qp).half.half.half

/-- **The revision tokens and the loan the writer's state keeps** (track A, request 3, 2026-11-06;
for a watchable store too, 2026-11-06: its writer needs nothing of its caller): `n` of the revision
budget's tokens (all not spent), the writer's loan (`writerLoan`), and the committed log `L` with a
change in every revision past the first two (so, with its receipt, below the receipts' bound: one
token is free). -/
def wrState (γ : StoreNames) (n : Nat) (L : Log) : IProp GF :=
  iprop(ownToks γ.revs n ∗ writerLoan γ ∗ ⌜L.length ≤ logCh L + 2⌝)

/-- **The rest of the revision tokens a write transaction holds** (track A, request 3, 2026-11-06;
the loan is the transaction's, `storeTxnWriteIs`'s `Hcres`). -/
def wrToks (γ : StoreNames) (n : Nat) (L : Log) : IProp GF :=
  iprop(ownToks γ.revs n ∗ ⌜L.length ≤ logCh L + 2⌝)

/-- **The writer's state** (D22 receiver epochs, S2, 2026-10-22; until then in the batch lock's
resource, which `store.Restore` never takes): the index writer's handle at the committed log
`ilog` with no pending change, half the committed-log ghost variable (the other half under
`s.revMu`), half the ghost of the log the bucket's view is of (the other half in the batch lock's
resource), half of `currentRev` (`store.Write` reads it under the batch lock and `s.mu` shared),
the certificate of `ilog`, half the revision budget's authority (the other half under `s.revMu`),
and a reader slot of the lessor. It is in the writer's invariant (`writerInv`), checked out by a
writer holding `s.mu` shared and the batch lock. -/
def writerL (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (ilog : Log) (ntok : Nat),
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hw" ∷ idxWriter γ.idx ilog [] ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hwv" ∷ ghostVar γ.wv (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "HY" ∷ slotY γ ilog ∗
    "Hrtk" ∷ wrState γ (2 ^ 63 - 3 - ilog.length) ilog)

/-! ### The batch lock's resource, late-bound (the real backend)

The backend's batch lock holds its client's resource `W` from the backend's creation, but the
store's `writerRes s γ` names the store's location and ghost names, which `NewStore` makes. So
the real backend is made with `W := lateW gx`: a registration slot, unset (half of `gx` at
`none`, the other half the backend's creator's: `lateReg gx`), then set by `NewStore`'s first
`Unlock` to the store's `(s, γ)` for good, with its `writerRes s γ` (`storeW_register`). -/

/-- The real backend's late-bound lock resource: unset, or set for good to a store `(s, γ)` with
its writer's resource. -/
def lateW (gx : GName) : IProp GF :=
  iprop(dghostVar gx (DFrac.own (1 : Qp).half) (none : Option (Loc × StoreNames)) ∨
    ∃ (s : Loc) (γ : StoreNames), dghostVar gx DFrac.discard (some (s, γ)) ∗ writerRes s γ)

/-- The right to register the store (the backend's creator's half of `gx`, unset). -/
def lateReg (gx : GName) : IProp GF :=
  dghostVar gx (DFrac.own (1 : Qp).half) (none : Option (Loc × StoreNames))

/-- The store's lock resource in its backend (`writerRes` itself for mvcc's assumed backend). -/
def storeW (s : Loc) (γ : StoreNames) : IProp GF :=
  match γ.kb with
  | none => writerRes s γ
  | some d => lateW d.gx

/-- The lock's resource before `NewStore`'s first `Unlock` (`lateW` for the real backend). -/
def kbWi (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => lateW d.gx

/-- The store `(s, γ)` is the one registered in its backend (persistent). -/
def storeRegd (s : Loc) (γ : StoreNames) : IProp GF :=
  match γ.kb with
  | none => iprop(True)
  | some d => dghostVar d.gx DFrac.discard (some (s, γ))

/-- **The write right's invariant's name** (question 5's core stage, part (1)). -/
abbrev mwN : Namespace := (nroot .@ "mvcc") .@ "mw"

/-- **The write right's invariant** (the Draft's `mwInvW`; review round 15's N1/N3; persistent, in
`physOk` through `physCmp` when the store compacts, allocated by `NewStore` after `restore` gives the
right back): the other half of the key's ghost variable, and the right when it is `true`. The halves
agree on where the right is, so no exclusivity of the right is needed. -/
def mwInv (γ : StoreNames) : IProp GF :=
  inv mwN iprop(∃ b : Bool, ghostVar γ.mwk (1 : Qp).half b ∗
    if b then kbMWf γ.kb γ.bucket else iprop(True))

/-- The right to register a store in the instance `kb`. -/
def kbRegRight (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => lateReg d.gx

/-! ### The writer's resource is timeless (M2's item 15: the registration's invariant opens without a
later credit, inside the backend's lock contracts) -/

/-- **The pending registration lent to a snapshot's freezer** (the snapshot image's (d),
2026-11-05): a quarter of the right to register (the freezer holds the other quarter, so the lock's
resource is not registered meanwhile) and a quarter of the frozen flag up (so a writer, which finds
the writer's invariant unfrozen, excludes it); the freezer holds the batch lock's writer's resource
through the snapshot. Only for the real backend. -/
def regLent (γ : StoreNames) : IProp GF :=
  match γ.kb with
  | none => iprop(False)
  | some d => iprop(dghostVar d.gx (DFrac.own (1 : Qp).half.half) (none : Option (Loc × StoreNames)) ∗
      ghostVar γ.api.frz (1 : Qp).half.half true)

/-- The registration's invariant's name. -/
abbrev regN : Namespace := (nroot .@ "mvcc") .@ "reg"

/-- **The store's registration in its backend, done or pending** (persistent; D22 receiver epochs,
S6, 2026-10-22; an invariant since M2's item 15, 2026-11-02): the store `(s, γ)` registered in its
backend's late-bound lock slot (`storeRegd`), or not yet, with the right to register it and the
batch lock's resource to deposit (`kbRegRight`, `writerRes`): after `store.Restore`, whose new
backend's batch lock holds its unregistered `lateW` (`Restore` does not take the batch lock), until
the first holder of the batch lock registers it (`storeW_open`: a writer's `LockInsideApply`,
`writerInv_checkout`, or in compaction mode the resumed or next compaction's). `NewStore`
registers at its first `Unlock`. (The snapshot image's (d), 2026-11-05) Or lent to a snapshot's
freezer, pending (`regLent`): its opener excludes it (`storeW_open`'s `LE`). In the writer's state and, in compaction mode, in `physOk`
(`physCmp`). -/
def writerReg (s : Loc) (γ : StoreNames) : IProp GF :=
  inv regN iprop(storeRegd s γ ∨ kbRegRight γ.kb ∗ writerRes s γ ∨ regLent γ)

/-- **The store's compaction facts in `physOk`** (the Draft's `physCmpW`, review round 15's N3, gated
by the mode): the write right's invariant and the store's registration in its backend (the swap from
`storeW`, which for the real backend reaches `writerRes` through it). (M2, the storage side, Q1 (a),
2026-10-30: the write-back supply is no longer here: `store.Compact` takes it per compaction, and
hands it to the job, `compactJobPre`.) -/
def physCmp (s : Loc) (γ : StoreNames) : IProp GF :=
  if kbCmpM γ.kb then iprop(mwInv γ ∗ writerReg s γ) else iprop(True)

/-- The writer's invariant's name. -/
abbrev writerN : Namespace := (nroot .@ "mvcc") .@ "writer"

/-- **The writer's invariant** (persistent; D22 receiver epochs, S2, 2026-10-22): the writer's
state checked in, or the batch lock's key with a reader's part of `s.mu`'s deposit ghost (a writer,
holding the batch lock and `s.mu` shared, has the state out). A writer finds the state in (it
holds the key: `writerInv_checkout`); so does the holder of `s.mu` exclusively (`store.Restore`,
which takes neither the batch lock nor a writer's state from it: all of the deposit ghost). (S5b) At
the current objects and physical names, with an eighth of the fraction of them: a writer finds the
state at its pin's (`writerInv_checkout`). (The restore plan's R5e) Or, while `store.Restore`
restores, all of `s.mu`'s deposit ghost (no writer checks out: its part would be too much) and half
the index's history's authority (no writer checks in: its index writer's handle has all of it;
`Restore` keeps the other half, so the history is still its own when it checks the state back in),
without an eighth of the current objects and names: `Restore` keeps it, so that, holding every
other eighth, it finds the invariant in this state when it moves them (`restore_switch`), and the
state, which it moves to the new backend and index, is `Restore`'s (`restore_takeover`,
`restore_finish`). (S6) Checked in
with the backend's registration
(`writerReg`: pending after a restore), checked out with the store registered (`storeRegd`, until
S6 in `physOk`: a restored backend is registered only at its first writer's lock). (Track A,
2026-11-06, the coordinator's (b)) The restoring state holds half the frozen flag down; the restorer
keeps the other half from the takeover to the finish, where it excludes a frozen state (`slotFl ½
true`) and rejoins the flag whole for the checked-in state. -/
def writerInvBody (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop((∃ (p : PhysNames) (o : StoreObjs),
    curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
    ((slotFl γ 1 false ∗
        (writerL s (γ.withPhys p) ∗ writerReg s (γ.withPhys p) ∨
          writerKey (γ.withPhys p) ∗ wDep γ ∗ storeRegd s (γ.withPhys p))) ∨
      slotFl γ (1 : Qp).half true ∗ slotF γ)) ∨
    ghostVar γ.wr 1 () ∗ (∃ h : List HistItem, monoListAuthOwn γ.idx.hist (1 : Qp).half h) ∗
      slotFr γ ∗ slotFl γ (1 : Qp).half false)

/-- The writer's invariant (`writerInvBody`). -/
def writerInv (s : Loc) (γ : StoreNames) : IProp GF :=
  inv writerN (writerInvBody s γ)

/-- **The committed log `log` is certified OK by the caller** (persistent; 2026-10-14, unit T1):
`NewStore`'s logs (at most two revisions), or an element of the caller's map `γ.cok`. -/
def certOk (γ : StoreNames) (log : Log) : IProp GF :=
  iprop(⌜log.length ≤ 2⌝ ∨ (W64 (log.length : Int)) ↪[γ.cok]□ log ∨ (W64 0) ↪[γ.cok]□ ([] : Log))

/-- **Every log is certified** (persistent): the map's free mode, the element `0 ↦ []` (a caller
that does not use the certificates mints it; no committed log has length `0`, so a caller that does,
the etcd server, never holds it). -/
def certFree (γ : StoreNames) : IProp GF := (W64 0) ↪[γ.cok]□ ([] : Log)

/-- `s.revMu`'s fraction of the committed log's authority, at its lock's fraction `q`: a quarter
for a watchable store's (the outer quarter is `s.mu`'s), a half otherwise. -/
def revQ (γ : StoreNames) (q : Qp) : Qp := if γ.watchQ then q.half.half else q.half

/-- **The compaction revision's physical lag** (M2's item 15, the lag state, 2026-11-02): `s.revMu`'s
part of `compactMainRev` holds `cp`, at most the compaction revision `c`; below it only in
`restore()`'s resumed compaction, from the restored finished record to `compactLockfree`'s
`updateCompactRev` (`store.Restore` holding `s.mu` and the watchable store's lock), with a quarter of
the lock's fraction of the watchable store's deposit ghost (`StoreNames.wsd`). That excludes every
other opener of `s.revMu`: a holder of `s.mu` has a part of `compactMainRev` at `c`
(`revMuBodyL_mu`), one of the watchable store's lock its deposit ghost whole (`revMuBodyL_wsd`). -/
def revLag (γ : StoreNames) (q : Qp) (c cp : Int) : IProp GF :=
  iprop(⌜-1 ≤ cp ∧ cp ≤ c⌝ ∗ if cp = c then iprop(True) else ghostVar γ.wsd q.half.half ())

/-- **`s.revMu`'s resource with the compaction revision's physical lag** (M2's item 15, the lag
state, 2026-11-02): `revMuBody` but for `compactMainRev`, at `cp`, at most the compaction revision
`c` and below it only with the lag's token (`revLag`). The lock holds it (`revMuCur`); an opener
finds `revMuBody` (`revMuBodyL_mu`, `revMuBodyL_wsd`) but `updateCompactRev`, which ends the lag. -/
def revMuBodyL (s : Loc) (γ γp : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (log : Log) (ntok : Nat) (c cp : Int),
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "#Hnev" ∷ idxNevLb γp.idx log ∗
    "#Hok" ∷ certOk γ log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketViewL γp q.half log ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own q.half) ntok ∗
    "%Hbudget" ∷ ⌜log.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlog" ∷ idxLogAuth γ.idx (revQ γ q) log ∗
    "Hcmp" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 cp : w64) : IProp GF) ∗
    "Hcrev" ∷ crevUB γ.idx q.half.half c ∗
    "#Hperm" ∷ crevPermAt γ c ∗
    "Hlag" ∷ revLag γ q c cp ∗
    "%Hc" ∷ ⌜-1 ≤ c ∧ c < log.length⌝ ∗
    "HX" ∷ slotX γ q log c)

/-- **`s.revMu`'s resource while `store.Restore` restores** (D22 receiver epochs, S3, 2026-10-22):
`Restore` sets `currentRev = 1` and `compactMainRev = -1` under `s.revMu` and releases it before the
restored revision is known (`kvstore.go:302-307`), so the lock holds only its parts of the two
counters, at any values; `Restore` holds the rest. No verified reader sees it: every reader of
`s.revMu` holds `s.mu` or a watchable store's `s.mu`, and with it a part of the fields' share with
the restoring flag down (`fieldShare`, `revMuInv_open`). -/
def revMuRest (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (v c : w64), (s.[store, go!"currentRev"] ↦{DFrac.own q.half} v : IProp GF) ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} c : IProp GF))

/-- **`s.revMu`'s resource, at the current physical names** at fraction `q` (D22 receiver epochs,
S5b): an eighth of the fraction of the store's current objects and names, at `p`, and the resource
`revMuBody` with the bucket's view and the index's count of `p`'s names. -/
def revMuCur (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (p : PhysNames) (o : StoreObjs), curAt (γ.withPhys p) (DFrac.own q.half.half.half) o ∗
    revMuBodyL s γ (γ.withPhys p) q)

/-- **`s.revMu`'s resource** at fraction `q` (D22 receiver epochs, S3, 2026-10-22): half its
fraction of the restoring flag, at `m`, and the resource at the current physical names
(`revMuCur`, `m = false`; S5b) or, while `store.Restore` restores, its parts of the counters
(`revMuRest`, `m = true`). -/
def revMuInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ m : Bool, dghostVar γ.rst (DFrac.own q.half) m ∗
    (if m then revMuRest s q else revMuCur s γ q))

/-- **The four fields `store.Restore` writes, at the objects `o`**, at the fraction `dq`
(D22 receiver epochs, S3: until then `↦□` in `isStore`). -/
def storeFields (s : Loc) (o : StoreObjs) (dq : DFrac) : IProp GF :=
  iprop("Hfb" ∷ (s.[store, go!"b"] ↦{dq} o.b : IProp GF) ∗
    "Hfidx" ∷ (s.[store, go!"kvindex"] ↦{dq}
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #o.ti : GoInterface) : IProp GF) ∗
    "Hfsch" ∷ (s.[store, go!"fifoSched"] ↦{dq} o.ssched : IProp GF) ∗
    "Hfstop" ∷ (s.[store, go!"stopc"] ↦{dq} o.sstop : IProp GF))

/-- **The store's stop channel is closed** (persistent; M2, the storage side, review round 3's F2):
the payload mvcc's store gives its scheduler (`schedule.NewFIFOScheduler.spec`'s `Pay`).
`NewStore`/`store.Restore` make the scheduler before the stop channel (`kvstore.go:309-310`), so the
payload names the channel through an agreement name `γx` (`StoreNames.sx`) the store allocates
first and fixes (discarded) once the channel is made; the channel's broadcast is then `Done`.
`Restore`/`Close` close `stopc` before `Stop`, so they have it for `Scheduler.Stop`; a job finding
its context cancelled learns it (`schedule.schedPay_elim`, `stopPayAt_done`). At the later-credit
instance (the channels' specs need it); nothing at the other, as `schedule.isFifoOf`. -/
def stopPay (γx : GName) : IProp GF :=
  match hlc, hG, sem with
  | .hasLC, hG', _ => iprop(∃ c : Loc, dghostVar γx DFrac.discard c ∗
      ∃ γc : ChanNames, ownBroadcastChan (hG := hG') c γc iprop(True) Broadcast.Done)
  | .hasNoLC, _, _ => iprop(True)

/-- **The payload's channel name, at home** (M2, the storage side, review round 4's S2.2, the
approval's item 34): the agreement name `γx` a store allocates for its scheduler's payload
(`StoreNames.sx`, fresh per scheduler) records the stop channel `o.sstop` (fixed once the channel
is made) and is the scheduler's payload's (`physOk`'s conjunct at the current objects `o`). -/
def stopPayAt (γx : GName) (γs : schedule.SchedNames) (o : StoreObjs) : IProp GF :=
  iprop(dghostVar γx DFrac.discard o.sstop ∗ schedule.schedPayIs γs (stopPay γx))

/-- **What the store's objects `o` are at its names `γ`** (persistent; D22 receiver epochs, S5b:
until then `isStore`'s, at the pinned objects): the backend's contract at `γ`'s view, tokens, put
condition and lock resource, with the batch lock's invariant recorded (`hookP`) and the deposit
witness; the tree index; the scheduler. A share of the fields holds it of the current objects
and names (`fieldShareAt`), and so do the compaction jobs' (`storeStopR`). (D22 receiver epochs, S6: the
store's registration in its backend, `storeRegd`, moved to the writer's invariant, `writerInv`: a
restored backend is registered only at its first writer's lock.) -/
def physOk (s : Loc) (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(∃ (Ph Dep : IProp GF),
    "#Hhook" ∷ hookP γ Ph ∗
    "#Hbk" ∷ isKeyBackendG o.b (bucketView γ) (storeRT γ) (storeWT γ) iprop(False)
      (storePutOk γ) (delKey γ)
      (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) Ph (hookFn γ) (storeReq γ) (storeRb γ) (storeBt γ)
      (kbSR γ.kb) (kbSRh γ.kb) (kbMWv γ.kb γ.bucket) (kbHookNilAt γ.kb) ∗
    "#Hdep" ∷ □ Dep ∗
    "#Hti" ∷ isTreeIndex o.ti γ.idx ∗
    "#HisSched" ∷ schedule.isFifo o.ssched γ.sch ∗
    -- (question 5's core stage, part (1)) the compaction facts, by the mode
    "#HmwP" ∷ physCmp s γ ∗
    -- (M2, the storage side, item 34) the scheduler's payload: its stop channel closed
    "#Hpay" ∷ stopPayAt γ.sx γ.sch o ∗
    -- (M2, the storage side, item 26) the logical mode is the current backend's
    "%Hcmt" ∷ ⌜kbCmpM γ.kb ↔ γ.cm = true⌝)

/-- **A share `q` of the fields `store.Restore` writes, at the objects `o` and the names `γ`**
(D22 receiver epochs, S5b): the four points-to at `o`, half the fraction of the store's current
objects and names at them (`curAt`: `o` and `γ`'s physical names are the current ones), half the
fraction of the restoring flag, down, and what the objects are (`physOk`). -/
def fieldShareAt (s : Loc) (γ : StoreNames) (q : Qp) (o : StoreObjs) : IProp GF :=
  iprop("Hcur" ∷ curAt γ (DFrac.own q.half) o ∗ "Hflds" ∷ storeFields s o (DFrac.own q) ∗
    "Hfrst" ∷ dghostVar γ.rst (DFrac.own q.half) false ∗ "#Hph" ∷ □ physOk s γ o)

/-- **A share `q` of the fields `store.Restore` writes** (D22 receiver epochs, S3; S5b: at the
current objects and physical names, whatever they are). `s.mu`'s resource holds half its fraction
(`muInv`; a transaction's part, `muHeld`), the right to close the store a quarter
(`storeCloser`), and a watchable store's `s.mu` a quarter (`syncWatchers` reads `s.store.b` under
it, not under `s.mu`): `NewStore` returns it. -/
def fieldShare (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (p : PhysNames) (o : StoreObjs), fieldShareAt s (γ.withPhys p) q o)

/-- The number of the store's readers (`NewStore` hands out one reader per slot of its pool), the
backend's reader tokens it holds: (2026-11-02, the backend-auth-split stage) the backend's counted
stock (`backend.rdStockN`, past the backend's pool of `rdPoolN`); until then all the backend's
`actualMaxReaders` slots. (Track A, 2026-11-06, the server's request, decided by the coordinator)
Two fewer: the backend's opener keeps two counted reader slots for good (the server's apply thread's
writes and its storage-version monitor, `etcdStorage_open.law`). -/
abbrev nReaders : Nat := backend.rdStockN - 2

/-- **A slot of the readers' pool** (D22 receiver epochs, S4, 2026-10-22; S5a: with the backend's
reader token): a reader slot of the store's index's lock (of the objects `o`'s index; S5b: the
current one, `readerPool`), and a reader token of the store's backend (`storeRT`: until S5a each reader held its own, so
a restore, which swaps the backend, could not hand out the new one's nor take the old ones back
for the old backend's `Close`). -/
def idxSlot (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(idxReader o.ti γ.idx ∗ storeRT γ)

/-- **The watchable store's deposit** (D22 receiver epochs, S5a): all of the watchable store's
deposit ghost (`StoreNames.wsd`, held by the watchable store's `s.mu` at its fraction,
`wsFields`): `syncWatchers`, holding that lock exclusively, deposits it in the readers' pool while
it has a slot out. -/
def wsDep (γ : StoreNames) : IProp GF := ghostVar γ.wsd 1 ()

/-- The readers' pool's invariant name. -/
abbrev poolN : Namespace := (nroot .@ "mvcc") .@ "readers"

/-- **The readers' pool** (D22 receiver epochs, S4, 2026-10-22: until then each reader held its slot
of the index's lock for good, `storeReaderC`, so a restore, which builds a new index, could not
hand out the new one's; S5a: each slot with a reader token of the backend): the slots not out, as
many as the idle readers' tickets (`tk`); for each slot out under `s.mu` a transaction's deposit of
its part of `s.mu`'s deposit ghost (`wDep`), as many as the transactions' tickets (`tko`); for each
slot out under the watchable store's lock the watchable store's deposit (`wsDep`, as many as
`tkw`'s tickets). A transaction checks a slot out with its ticket (`readerPool_checkout`, under
`s.mu` shared) and back in at `End`; `syncWatchers` under the watchable store's lock
(`readerPool_checkout_ws`); a reader may also retire its ticket for a backend token of its own
(`readerPool_retire`: the apply thread's, for its writes under the batch lock, and the storage
version monitor's). The holder of `s.mu` exclusively and of the watchable store's lock
(`store.Restore`) finds every slot not retired in. (S5b) The slots are of the current objects and
names (`readerPool`): a lender checks out at a part of them (its pin). (D22 receiver epochs, S8d,
W7, 2026-10-25) The slots in, out and retired are exactly `nReaders`, and the retired count `r` is
known to the store's creator (half of `γ.tkr`, `retiredAt`; until then an upper bound and retired
tickets), so that a restore returns exactly the old backend's tokens it held and the creator knows
how many: with the retired ones, all of them, for the old backend's `Close`. -/
def poolBody (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(∃ k j w r : Nat, ownTokAuth γ.tk k ∗ ownTokAuth γ.tko j ∗ ownTokAuth γ.tkw w ∗
    ghostVar γ.tkr (1 : Qp).half r ∗
    ([∗list] _x ∈ List.replicate k (), idxSlot γ o) ∗
    ([∗list] _x ∈ List.replicate j (), wDep γ) ∗
    ([∗list] _x ∈ List.replicate w (), wsDep γ) ∗ ⌜k + j + w + r = nReaders⌝)

/-- The readers' pool's invariant (S5b): its body at the current objects and names, with an eighth
of the fraction of them. -/
def readerPool (γ : StoreNames) : IProp GF :=
  inv poolN iprop(∃ (p : PhysNames) (o : StoreObjs),
    curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗ poolBody (γ.withPhys p) o)

/-- `s.mu`'s resource at fraction `q`, at the compaction revision `c` (`-1`: none): half
`compactMainRev`'s points-to and a quarter of the compaction revision's authority (`s.revMu`
holds as much; the compaction right, half the authority, is `compactRightR`), with a certified
log of which `c` is a revision (`crevSafe`; 2026-10-13, unit 6a). A transaction holds `s.mu`
shared for its whole life, so its `rangeKeys` reads `compactMainRev` from its part (`muHeld`). -/
def muInvAt (s : Loc) (γ : StoreNames) (q : Qp) (c : Int) : IProp GF :=
  iprop("HcmpM" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 c : w64) : IProp GF) ∗
    "HcrevM" ∷ crevUB γ.idx q.half.half c ∗
    "HwcM" ∷ api.wcrPart γ.api q.half c ∗
    "#HclM" ∷ crevSafe γ c ∗
    "#HpM" ∷ crevPermAt γ c ∗
    "%HcM" ∷ ⌜-1 ≤ c⌝)

/-- `s.mu`'s resource at fraction `q`: at some compaction revision, and the writer's deposit
ghost at the fraction (D22 receiver epochs, S2: a holder of `s.mu` exclusively has all of it, so
no writer has the writer's state out, `writerInv`). -/
def muInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ c : Int, muInvAt s γ q c ∗ ghostVar γ.wr q () ∗ fieldShare s γ q.half)

/-- `s.mu` held shared by a transaction, at the compaction revision `c`: the reader's token and
its part of `s.mu`'s resource (given back at `End`), its share of the fields at the current
objects, whose index is `ti`, and names, `γ`'s (D22 receiver epochs, S5b: a transaction is at the
names its `s.mu` share pins; until then the index's pin `idxPin`). -/
def muHeld (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) : IProp GF :=
  iprop(sync.ownRWMutexRLocked (muAddr s) (muInv s γ) ∗ muInvAt s γ sync.rfrac c ∗
    ∃ o : StoreObjs, ⌜o.ti = ti⌝ ∗ fieldShareAt s γ sync.rfrac.half o)

/-- A store (persistent): its lessor, logger, and the two locks' guards; and what compaction uses:
the configuration (a positive `CompactionBatchLimit`: the job's loop needs it to end,
`nonissues/etcd-compaction-negative-batch-limit.md`), the hash storage. **Nothing of its objects and
physical names** (D22 receiver epochs, S5b, 2026-10-22: until then the backend of its instance
`γ.kb`, registered, with the batch lock's deposit witness, the batch lock's invariant `hookP`, the
index, the scheduler, at the pinned objects): they are the current ones, which `store.Restore`
replaces, so they are in the shares of the locks guarding their readers (`fieldShareAt`'s
`physOk`, at a part of the store's current objects and names, `curAt`), and `isStore s γ` reads
only `γ`'s logical names (`isStore_withPhys`). **The four fields `store.Restore` writes** (`b`,
`kvindex`, `fifoSched`, `stopc`) are not here either (S3: until then `↦□`): their points-to are
shared by the locks (`fieldShare`). The scheduler's stop token is the right to close's
(`storeCloser`, D19m (C), 2026-10-18), which a compacting store keeps in its compaction right
(`compactRightR`, M2's item 17). The fields `restore` and `Close` change are fixed here (out of scope).
`compactMainRev` is under the two locks (`muInv`, `revMuInv`); and the certificate of the initial
log `[[], []]` (`NewStore`'s: revision 1, `currentRev = 1`), so every committed log extends it.
The time receipts' bound is at most `2 ^ 48` (D19c, 2026-10-18: `NewStore`'s premise): a write
transaction's index writer holds a receipt per change, so its pending changes stay below the
backend's bound on a session's puts (`putMax`) without a premise on the transaction's size. -/
def isStore (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (le : GoInterface) (lg : Loc) (scfg : StoreConfig) (shs : Loc),
    "#Hle" ∷ s.[store, go!"le"] ↦□ le ∗
    "#Hlessor" ∷ isLessor le γ.leases ∗
    "#Hlg" ∷ s.[store, go!"lg"] ↦□ lg ∗
    "#Hlgnn" ∷ zapLoggerOk lg ∗
    "#Hmu" ∷ sync.isRWMutexGuard (muAddr s) (muInv s γ) ∗
    "#HrevMu" ∷ sync.isRWMutexGuard (revMuAddr s) (revMuInv s γ) ∗
    "#Hcfg" ∷ s.[store, go!"cfg"] ↦□ scfg ∗
    "%Hcfgl" ∷ ⌜0 < sint.Z scfg.CompactionBatchLimit' ∧ sint.Z scfg.CompactionBatchLimit' ≤ rangeLimitMax⌝ ∗
    "#Hhashes" ∷ s.[store, go!"hashes"] ↦□
      (interface.mkOk (go.GoType.PointerType hashStorage.ty) #shs : GoInterface) ∗
    "#HhsOk" ∷ mvcc.hashStorageOk shs ∗
    "#Hwi" ∷ writerInv s γ ∗
    "#Hpool" ∷ readerPool γ ∗
    "#Hc0" ∷ idxCert γ.idx [[], []] ∗
    "%Hrb" ∷ ⌜receiptBound GF ≤ 2 ^ 48⌝)

/-- A transaction's tokens, for a store that may be compacted: a reader slot of each of `s.mu` and
`s.revMu`, and a ticket of the readers' pool (D22 receiver epochs, S4: the pool hands out a slot
of the index's lock for the transaction, `readerPool`; S5a: with a reader's token of the backend,
`storeRT`, until then the reader's own, so that a restore can swap the backend's tokens). **The reader the
store's specs take** (2026-10-13, unit 6a: `store.Read`/`Write`/`Rev`, the read view's; a
transaction's `End` gives it back): its transactions observe the compaction revision, which may
move (`store.Compact`, by the holder of the compaction right). -/
def storeReaderC (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop("Hmu" ∷ sync.ownRWMutex (muAddr s) (muInv s γ) ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Htk" ∷ ownToks γ.tk 1)

/-! ## The read transaction -/

/-- The `storeTxnRead` of a read transaction at revision `rev` of the committed log `log`,
which observed the compaction revision `crev` (its fields, read-only): its reader `rt` (as
`UnsafeReader` and as `ReadTx`; a snapshot of a bucket holding `log`'s, but for keys compaction
may have deleted, `txReader`), `firstRev` is `crev` (`store.Read` reads it from
`s.compactMainRev`), `rev` is `log`'s last revision, `crev` one of its revisions (or `-1`), and
the reader's tag `Z` (persistent, carried from `store.Read` to `End`: the frozen readers'
`crevFrozen γ`, `True` for a compacting client's), and the index's count of the log's events
(`idxNevLb`, read under `s.revMu` with the log: a certificate no longer says it; D22 receiver
epochs, S1).

The tag `Z` defaults to `True` (M2, `notes/m2-plan.md`, S1, 2026-10-27; until then `crev` defaulted
to `-1` and `Z` to `crevFrozen γ`, the transaction of a store never compacted, as the packages
above mvcc used it). -/
def storeTxnReadIs (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames) (log : Log)
    (rev : w64) (crev : Int) (Z : IProp GF := iprop(True)) : IProp GF :=
  iprop("#Hs" ∷ (txCommon tr).[storeTxnCommon, go!"s"] ↦□ s ∗
    "#Htxc" ∷ (txCommon tr).[storeTxnCommon, go!"tx"] ↦□ (GoInterface.ok rt : GoInterface) ∗
    "#HfirstRev" ∷ (txCommon tr).[storeTxnCommon, go!"firstRev"] ↦□ (W64 crev : w64) ∗
    "#Hrev" ∷ (txCommon tr).[storeTxnCommon, go!"rev"] ↦□ rev ∗
    "#Htrace" ∷ (txCommon tr).[storeTxnCommon, go!"trace"] ↦□ trace ∗
    "#Htx" ∷ tr.[storeTxnRead, go!"tx"] ↦□ (GoInterface.ok rt : GoInterface) ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "#Hnev" ∷ idxNevLb γ.idx log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "%Hrev" ∷ ⌜rev = W64 ((log.length : Int) - 1)⌝ ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "%Hcrev" ∷ ⌜-1 ≤ crev ∧ crev < log.length⌝ ∗
    "#HZ" ∷ □ Z)

/-- A read transaction's reader `rt`, locked: a snapshot `m'` of a bucket `m` holding `log`'s,
but for keys compaction may have deleted (`snapThin`; 2026-10-13, unit 6a), with the reader's
token (from its `RLock` to the transaction's `End`, which `RUnlock`s it, getting the store's
reader token back), and the transaction's part of `s.mu`'s deposit ghost (given back at `End`
with its part of `s.mu`'s resource; D22 receiver epochs, S2). -/
def txReader (γ : StoreNames) (rt : GoInterfaceOk) (log : Log) : IProp GF :=
  iprop(∃ (m m' : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
    "#Hsnap" ∷ keyReadLocked (storeRT γ) iprop(False) false rt m' Rd Tok ∗
    "#Hthin" ∷ snapThin m m' (delKey γ) ∗
    "Htok" ∷ Tok ∗
    "Hwr" ∷ wDep γ ∗
    "Htko" ∷ ownToks γ.tko 1 ∗
    "%Hsub" ∷ ⌜GMap.Subseteq (bucketMap log) m⌝)

/-- **The `mvcc.KV` `kv` over the store `s`** (persistent; unit N4, D14a): the store itself, or a
watchable store `ws` whose embedded `store` is `s` (whose `Read`, promoted, is `s`'s:
`KVView.lean`). -/
def kvOver (kv : GoInterface) (s : Loc) : IProp GF :=
  iprop(⌜kv = interface.mkOk (go.GoType.PointerType store.ty) #s⌝ ∨
    ∃ ws : Loc, ⌜kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #ws⌝ ∗
      ws.[watchableStore, go!"store"] ↦□ s)

/-- The store's `readView` (`kv_view.go`): its `kv` is a KV over the store `s` (`kvOver`: the
store itself, as `NewStore` makes it, or the watchable store `newWatchableStore` points it at;
unit N4, D14a: it was the store only). -/
def isReadView (rv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ kv : GoInterface, "#Hkv" ∷ rv.[readView, go!"kv"] ↦□ kv ∗ "#Hkvo" ∷ kvOver kv s ∗
    "#Hs" ∷ isStore s γ)

/-! ## The result of a range read -/

/-- A fresh `*mvccpb.KeyValue` holding the model's `kv`: all its fields (`full`), or, for a
keys-only read, its key and revisions and version (value and lease zero); the key and value
as read-only slices. -/
def kvPtrIs (full : Bool) (p : Loc) (kv : EtcdKv) : IProp GF :=
  iprop(∃ (ks : GoSlice) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (uf : GoSlice) (sc : w32),
    ks ↦*□ kv.key ∗
    if full then
      ∃ vs : GoSlice, vs ↦*□ kv.value ∗
        p ↦ ({
          state' := st, Key' := ks, CreateRevision' := kv.createRev, ModRevision' := kv.modRev,
          Version' := kv.version, Value' := vs, Lease' := kv.lease, unknownFields' := uf,
          sizeCache' := sc } : go_etcd_io.etcd.api.v3.mvccpb.KeyValue)
    else
      p ↦ ({
        state' := st, Key' := ks, CreateRevision' := kv.createRev, ModRevision' := kv.modRev,
        Version' := kv.version, Value' := slice.nil, Lease' := W64 0, unknownFields' := uf,
        sizeCache' := sc } : go_etcd_io.etcd.api.v3.mvccpb.KeyValue))

/-! ## The write transaction -/

/-- **The write transaction's lock token** at the puts `l`: the batch transaction's (`Locked l`),
or, after the lessor's delete from the `Lease` bucket (`ld`: `batchTxSpecG`'s last clause;
leases T3, 2026-10-25), a token only `Unlock` takes (`unlockAt`). -/
abbrev lockedIs (ld : Bool) (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W P : IProp GF)
    (Locked : Puts → IProp GF) (l : Puts) : IProp GF :=
  match ld with
  | false => Locked l
  | true => iprop(∃ U : IProp GF, U ∗ unlockAt bt View W P U l)

/-- The `*mvccpb.KeyValue`s of a write transaction's `changes`: the `i`-th holds what the
`i`-th pending change wrote (`changeKv`: the new key-value of a put, the key alone of a
delete). -/
def changesAre (ps : List Loc) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop([∗list] i ↦ p ∈ ps, ∃ kv : EtcdKv,
    ⌜changeKv (W64 ilog.length) (stateAfter ilog) pend i = some kv⌝ ∗ kvPtrIs true p kv)

/-- The `storeTxnWrite` at `tw` of a write transaction of the store `s` at the committed log
`ilog`, with the pending changes `pend` (the next revision's, not yet visible to readers): its
fields (`beginRev` is `ilog`'s last revision, `changes` the key-values written), the batch
transaction locked with the pending puts, the writer's state (`writerL`, checked out of
`writerInv`, with the pending changes in the index writer's handle) and the batch lock's resource
(`writerRes`: the view's quarter, the compaction's part; its key deposited in `writerInv`), the
writer's API slot (`slotY`, carried from `Write` to `End`: strict M1, 2026-11-04), with
the writer's pin (its quarter of the view, and its loan with the compaction's part: `writerLoan`;
M2's item 37), both halves of the view's log ghost, the revision token the transaction was opened with, and the
transaction's tokens (with its slot of the index's lock, out of the readers' pool): `s.mu` held shared at the compaction revision `crev` the
transaction observed (one of `ilog`'s revisions, or `-1`), and the reader's tag `Z` (persistent,
given back at `End`). By default the frozen transaction (`crev = -1`, `Z = crevFrozen γ`: a store
never compacted, as the packages above mvcc state it; 2026-10-13, unit 6a). (M4, track B,
2026-11-06) The batch lock's invariant by the store's name of it (`hookP`), not the hook's facts: a
store without a hook has none (`store.Write`'s nil arm). -/
def storeTxnWriteIs (tw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (crev : Int) (Z : IProp GF := iprop(True)) (ld : Bool := false) : IProp GF :=
  iprop(∃ (ti : Loc) (bt : GoInterfaceOk) (Locked : Puts → IProp GF) (chs : GoSlice)
    (ps : List Loc) (ntok : Nat) (Pw : IProp GF) (fw : val) (Dep : IProp GF),
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Htok" ∷ revToken γ ∗
    "Htw" ∷ tw ↦ ({
        storeTxnCommon' := {
          s' := s, tx' := GoInterface.ok bt, firstRev' := W64 0, rev' := W64 0, trace' := trace },
        tx' := GoInterface.ok bt, beginRev' := W64 ((ilog.length : Int) - 1),
        changes' := chs } : storeTxnWrite) ∗
    "Hchs" ∷ chs ↦* ps ∗
    "Hcap" ∷ ownSliceCap Loc chs (DFrac.own 1) ∗
    "%Hps" ∷ ⌜ps.length = pend.length⌝ ∗
    "Hkvs" ∷ changesAre ps ilog pend ∗
    "#Hs" ∷ isStore s γ ∗
    "#Hhook" ∷ hookP γ Pw ∗
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw (hookFn γ) (storeRb γ) (kbMWv γ.kb γ.bucket) ∗
    "#HbtB" ∷ storeBt γ bt ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "Hrt" ∷ storeRT γ ∗
    "Hlocked" ∷ lockedIs ld bt (bucketView γ) (storeW s γ) Pw Locked (pendPuts ilog pend) ∗
    "Hw" ∷ idxWriter γ.idx ilog pend ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketViewL γ txQ ilog ∗
    "Hwv" ∷ ghostVar γ.wv 1 ilog ∗
    "HY" ∷ slotY γ ilog ∗
    "Htko" ∷ ownToks γ.tko 1 ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hmu" ∷ muHeld s γ crev ti ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "Hcres" ∷ (compactRes γ ilog ∗ writerLoan γ ∗ wrToks γ (2 ^ 63 - 4 - ilog.length) ilog) ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "%Hcrev" ∷ ⌜-1 ≤ crev ∧ crev < ilog.length⌝ ∗
    "#HZ" ∷ □ Z)

/-- The log a write transaction commits at `End`: the pending revision appended, if it has a
change (else no revision is made). -/
def commitLog (ilog : Log) (pend : List Change) : Log :=
  if pend = [] then ilog else ilog ++ [pend]

section wrlemmas
open Iris.ProofMode

end wrlemmas

/-- The store's `writeView` (`kv_view.go`): its `kv` is the store `s`. -/
def isWriteView (wv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop("#Hkv" ∷ wv.[writeView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType store.ty) #s : GoInterface) ∗
    "#Hs" ∷ isStore s γ)

/-! ## `restore` of a key bucket with data (D22 S-g) -/

end reprs

section hookLc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A stop channel (persistent): a broadcast channel of `True`, maybe closed (the store's
`stopc`; the watchable store's). Moved from `InvWatchStore.lean` (2026-10-13). -/
def isStopChan (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan c γc iprop(True) Broadcast.Unknown)

end hookLc

section halves
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

end halves

/-- Normalizes the projections of `γ.withPhys p` (D22 receiver epochs, S5b): a logical name to
`γ`'s, a physical one to `p`'s. -/
macro "withPhys_simp" : tactic => `(tactic| simp only [Perennial.EtcdGrove.mvcc.isStore_withPhys, Perennial.EtcdGrove.mvcc.crevSafe_withPhys, Perennial.EtcdGrove.mvcc.muInvAt_withPhys,
    Perennial.EtcdGrove.mvcc.storeReaderC_withPhys, Perennial.EtcdGrove.mvcc.storeReader_withPhys, Perennial.EtcdGrove.mvcc.crevFrozen_withPhys,
    Perennial.EtcdGrove.mvcc.revMuInv_withPhys, Perennial.EtcdGrove.mvcc.idxCert_withPhys, Perennial.EtcdGrove.mvcc.idxSealed_withPhys,
    Perennial.EtcdGrove.mvcc.idxLogAuth_withPhys, Perennial.EtcdGrove.mvcc.crevUB_withPhys, Perennial.EtcdGrove.mvcc.crevLb_withPhys, Perennial.EtcdGrove.mvcc.certOk_withPhys,
    Perennial.EtcdGrove.mvcc.delKey_withPhys, Perennial.EtcdGrove.mvcc.revToken_withPhys, Perennial.EtcdGrove.mvcc.muInv_withPhys, Perennial.EtcdGrove.mvcc.writerInv_withPhys,
    Perennial.EtcdGrove.mvcc.readerPool_withPhys, Perennial.EtcdGrove.mvcc.wDep_withPhys, Perennial.EtcdGrove.mvcc.wsDep_withPhys, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_clog, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_leases, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_revs, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_cok, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_watchQ, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_wr, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_cur, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_rst, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tk, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tko, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_wsd, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tkw, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tkr, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_cm, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_idx_hist, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_idx_log, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_idx_crev])

section physShare
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

end physShare

/-! ## The compaction keys' write right: the swap (question 5's core stage, part (1)) -/

section mwLc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

end mwLc

end mvcc
end EtcdGrove
end Perennial
