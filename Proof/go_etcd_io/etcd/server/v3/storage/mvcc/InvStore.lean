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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.DGhostVar
public import Perennial.Proof.TokSet
public import Perennial.Proof.context
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevOrder
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LeaseItems

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- The `Key` bucket's written-back contents: a revision's bytes to the encoded key-value. -/
abbrev Bucket := GMap GoString GoString

/-- The `Key` bucket's name. -/
abbrev keyName : GoString := go_etcd_io.etcd.server.v3.storage.schema.keyName

/-- **The real backend's instance** (2026-10-13, unit 5): the store over etcd's backend
(`storage/backend`, proved over bbolt's key-value contract; `BackendBridge.lean`), named by data:
the backend's ghost names `γB`, its parameters but the fixed ones (the clients' bucket table
`BT`, the hook's bound `hookMax`, the batch limit `limit`: the hook's buckets are all but `Key`,
the safe-range bucket is `Key`), the backend's location `be`, and the name `gx` of the batch
lock's late-bound resource (`lateW`: the store registers its own at `NewStore`'s first
`Unlock`). -/
structure KBReal where
  γB : backend.BNames
  BT : GMap GoString w64
  hookMax : Nat
  limit : w64
  be : Loc
  gx : GName

/-- **etcd's rest buckets**: the buckets the server's stores keep besides `Key` and `Meta` (the
lessor's `lease`, the alarm store's `alarm`, the auth store's `auth`, `authUsers`, `authRoles`,
the membership's `members`, `members_removed`, `cluster`), which a snapshot's receiver recovers
(D22 S-f). -/
def restBuckets : List GoString :=
  [go!"lease", go!"alarm", go!"auth", go!"authUsers", go!"authRoles", go!"members",
   go!"members_removed", go!"cluster"]

/-- The backend's parameters of a real instance: the hook's buckets all but `Key`, `Key` the one
safe-range bucket, the hook's own keys the consistent index's two in `Meta` (2026-10-13, unit 7:
only the server's pre-commit hook writes them), the tracked buckets the rest buckets (D22,
2026-10-23: the backend over every bucket). -/
def KBReal.P (d : KBReal) : backend.BParams :=
  { BT := d.BT, HB := fun n => decide (n ≠ keyName), SB := fun n => decide (n = keyName),
    HK := fun n k => decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧
      (k = go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes)),
    RB := fun n => decide (n ∈ restBuckets),
    hookMax := d.hookMax, limit := d.limit }

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

instance idxNames_countable : Pos.Countable IdxNames :=
  countableOfLeftInverse (fun x : IdxNames => (x.hist, x.nev, x.log, x.crev, x.cmp))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

instance schedNames_countable : Pos.Countable schedule.SchedNames :=
  countableOfLeftInverse (fun x : schedule.SchedNames => (x.run, x.jobs)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance dbNames_countable : Pos.Countable backend.DBNames :=
  countableOfLeftInverse (fun x : backend.DBNames => (x.db, x.wr)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

instance bNames_countable : Pos.Countable backend.BNames :=
  countableOfLeftInverse
    (fun x : backend.BNames => (x.fk, x.dlb, x.dlg, x.cln, x.rbk, x.hkd, x.db, x.view, x.rd, x.hist, x.cached, x.cur, x.hook,
      x.opn, x.wb, x.rdt, x.txa, x.txb, x.rvs, x.cvw, x.wbc, x.used, x.cls, x.sdn, x.stk))
    (fun r => let r' := r.2; let r0 := r'.2; let q0 := r0.2; let q := q0.2; let p := q.2; ⟨p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, p.1, q.1, q0.1, r0.1, r'.1, r.1⟩)
    (fun _ => rfl)

instance kbReal_countable : Pos.Countable KBReal :=
  countableOfLeftInverse (fun x : KBReal => (x.γB, x.BT, x.hookMax, x.limit, x.be, x.gx))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

instance storeNames_countable : Pos.Countable StoreNames :=
  countableOfLeftInverse
    (fun x : StoreNames => ((x.idx, x.bucket, x.clog, x.leases, x.revs, x.hook, x.hookFn, x.kb, x.cmeta, x.fin, x.sch, x.cok, x.watchQ, x.wr, x.wk, x.wv, x.cur, x.rst, x.tk, x.tko, x.wsd, x.tkw), x.tkr))
    (fun q => let p := q.1; ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, q.2⟩)
    (fun _ => rfl)

/-- **The store's physical ghost names** (D22 receiver epochs, S5b, 2026-10-22): those of one
backend (`kb`, the bucket's view `bucket`, the batch lock's invariant `hook` and the hook
`hookFn`, the batch lock's key `wk` and view log `wv`, the compaction's meta keys `cmeta` and
finished counter `fin`), one index (`nev`, `cmp`) and one scheduler (`sch`): what `store.Restore`
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

instance physNames_countable : Pos.Countable PhysNames :=
  countableOfLeftInverse
    (fun x : PhysNames => (x.nev, x.cmp, x.bucket, x.hook, x.hookFn, x.kb, x.cmeta, x.fin, x.sch, x.wk, x.wv))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- The physical names of the store's names `γ`. -/
def StoreNames.phys (γ : StoreNames) : PhysNames :=
  ⟨γ.idx.nev, γ.idx.cmp, γ.bucket, γ.hook, γ.hookFn, γ.kb, γ.cmeta, γ.fin, γ.sch, γ.wk, γ.wv⟩

/-- **The store's names `γ` at the physical names `p`** (S5b): the logical names `γ`'s. -/
def StoreNames.withPhys (γ : StoreNames) (p : PhysNames) : StoreNames :=
  ⟨⟨γ.idx.hist, p.nev, γ.idx.log, γ.idx.crev, p.cmp⟩, p.bucket, γ.clog, γ.leases, γ.revs, p.hook,
    p.hookFn, p.kb, p.cmeta, p.fin, p.sch, γ.cok, γ.watchQ, γ.wr, p.wk, p.wv, γ.cur, γ.rst, γ.tk,
    γ.tko, γ.wsd, γ.tkw, γ.tkr⟩

@[simp] theorem StoreNames.withPhys_phys (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).phys = p := rfl

@[simp] theorem StoreNames.withPhys_self (γ : StoreNames) : γ.withPhys γ.phys = γ := rfl

@[simp] theorem StoreNames.withPhys_withPhys (γ : StoreNames) (p p' : PhysNames) :
    (γ.withPhys p).withPhys p' = γ.withPhys p' := rfl

@[simp] theorem StoreNames.withPhys_clog (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).clog = γ.clog := rfl

@[simp] theorem StoreNames.withPhys_leases (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).leases = γ.leases := rfl

@[simp] theorem StoreNames.withPhys_revs (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).revs = γ.revs := rfl

@[simp] theorem StoreNames.withPhys_cok (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).cok = γ.cok := rfl

@[simp] theorem StoreNames.withPhys_watchQ (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).watchQ = γ.watchQ := rfl

@[simp] theorem StoreNames.withPhys_wr (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).wr = γ.wr := rfl

@[simp] theorem StoreNames.withPhys_cur (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).cur = γ.cur := rfl

@[simp] theorem StoreNames.withPhys_rst (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).rst = γ.rst := rfl

@[simp] theorem StoreNames.withPhys_tk (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).tk = γ.tk := rfl

@[simp] theorem StoreNames.withPhys_tko (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).tko = γ.tko := rfl

@[simp] theorem StoreNames.withPhys_wsd (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).wsd = γ.wsd := rfl

@[simp] theorem StoreNames.withPhys_tkw (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).tkw = γ.tkw := rfl

@[simp] theorem StoreNames.withPhys_tkr (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).tkr = γ.tkr := rfl

@[simp] theorem StoreNames.withPhys_idx_hist (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).idx.hist = γ.idx.hist := rfl

@[simp] theorem StoreNames.withPhys_idx_log (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).idx.log = γ.idx.log := rfl

@[simp] theorem StoreNames.withPhys_idx_crev (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).idx.crev = γ.idx.crev := rfl

@[simp] theorem StoreNames.withPhys_bucket (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).bucket = p.bucket := rfl

@[simp] theorem StoreNames.withPhys_hook (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).hook = p.hook := rfl

@[simp] theorem StoreNames.withPhys_hookFn (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).hookFn = p.hookFn := rfl

@[simp] theorem StoreNames.withPhys_kb (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).kb = p.kb := rfl

@[simp] theorem StoreNames.withPhys_cmeta (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).cmeta = p.cmeta := rfl

@[simp] theorem StoreNames.withPhys_fin (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).fin = p.fin := rfl

@[simp] theorem StoreNames.withPhys_sch (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).sch = p.sch := rfl

@[simp] theorem StoreNames.withPhys_wk (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).wk = p.wk := rfl

@[simp] theorem StoreNames.withPhys_wv (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).wv = p.wv := rfl

@[simp] theorem StoreNames.withPhys_idx_nev (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).idx.nev = p.nev := rfl

@[simp] theorem StoreNames.withPhys_idx_cmp (γ : StoreNames) (p : PhysNames) :
    (γ.withPhys p).idx.cmp = p.cmp := rfl


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
/-- The address of a `storeTxnWrite`'s embedded `storeTxnCommon`. -/
abbrev txCommonW (tw : Loc) : Loc := structFieldRef storeTxnWrite go!"storeTxnCommon" tw

end addrs

/-- Two interface values of the same pointer type are the same pointer (with its own binders:
nothing in its statement determines a section's `GF`). -/
theorem mkOk_loc_inj [GooseExts] [GoLocalContext] [GoGlobalContext] [go.Semantics] (T : go.GoType)
    {a b : Loc}
    (h : interface.mkOk T #a = interface.mkOk T #b) : a = b := by
  unfold interface.mkOk at h
  simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact go.intoVal_inj h


section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's current objects and physical names are `o` and `γ`'s**, at the fraction `dq`
(D22 receiver epochs, S5b: until then `objsPin`, a discarded pin of the objects): a part of the
store's ghost variable `cur`, which every share of the locks guarding a reader of the objects holds
(`fieldShare`, `revMuBody`, `writerInv`, `readerPool`) and the writer's fragment (`writerFrag`),
so that they agree on them, and `store.Restore`, which gathers them all, can move them. A
predicate at names `γ` with such a part is of the current backend, index and scheduler. -/
def curAt (γ : StoreNames) (dq : DFrac) (o : StoreObjs) : IProp GF :=
  dghostVar γ.cur dq ((o, γ.phys) : StoreObjs × PhysNames)

/-- Two parts of the current objects and names agree. -/
theorem curAt_agree (γ γ' : StoreNames) (h : γ.cur = γ'.cur) (dq dq' : DFrac) (o o' : StoreObjs) :
    curAt (GF := GF) γ dq o ∗ curAt γ' dq' o' ⊢ ⌜o = o' ∧ γ.phys = γ'.phys⌝ := by
  unfold curAt
  rw [h]
  iintro ⟨H1, H2⟩
  ihave %Hv := dghostVar_agree γ'.cur _ dq _ dq' $$ H1 H2
  ipureintro
  simp only [Prod.mk.injEq] at Hv
  exact Hv

/-- **A pin agrees with a part at some physical names**: they are the pin's. -/
theorem curAt_pin (γ : StoreNames) (p : PhysNames) (dq dq' : DFrac) (o o' : StoreObjs) :
    curAt (GF := GF) γ dq o ∗ curAt (γ.withPhys p) dq' o' ⊢ ⌜o' = o ∧ p = γ.phys⌝ := by
  iintro H
  ihave %Hv := curAt_agree γ (γ.withPhys p) rfl dq dq' o o' $$ H
  ipureintro
  exact ⟨Hv.1.symm, by have h2 := Hv.2; simp only [StoreNames.withPhys_phys] at h2; exact h2.symm⟩

/-- Two parts of the current objects and names at the same names: the same objects. -/
theorem curAt_agree_o (γ : StoreNames) (dq dq' : DFrac) (o o' : StoreObjs) :
    curAt (GF := GF) γ dq o ∗ curAt γ dq' o' ⊢ ⌜o = o'⌝ := by
  iintro H
  ihave %Hv := curAt_agree γ γ rfl dq dq' o o' $$ H
  ipureintro; exact Hv.1

instance curAt_fractional (γ : StoreNames) (o : StoreObjs) :
    Fractional (fun q => curAt (GF := GF) γ (DFrac.own q) o) := by
  unfold curAt; exact dghostVar_fractional (GF := GF) γ.cur _

instance curAt_discard_persistent (γ : StoreNames) (o : StoreObjs) :
    Persistent (curAt (GF := GF) γ DFrac.discard o) := by
  unfold curAt; infer_instance

/-- Two halves of a part of the current objects and names. -/
theorem curAt_halves (γ : StoreNames) (q : Qp) (o : StoreObjs) :
    curAt (GF := GF) γ (DFrac.own q) o ⊣⊢ curAt γ (DFrac.own q.half) o ∗ curAt γ (DFrac.own q.half) o := by
  have h := (curAt_fractional (GF := GF) γ o).fractional q.half q.half
  rw [Qp.half_add_half] at h
  exact h

/-- **The writer's fragment** (D22 receiver epochs, S5b): an eighth of the store's current objects
and names, at `γ`'s: the store's names `γ` are the current ones for the holder, the sole writer
(`hookIs`, which `store.Write` takes and returns; `store.Restore` will take it and return it at the
new names). `NewStore` returns it. -/
def writerFrag (γ : StoreNames) : IProp GF :=
  iprop(∃ o : StoreObjs, curAt γ (DFrac.own (1 : Qp).half.half.half) o)

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
over such data (`bkNoCmp_of_fkOwn`), and under which a held reader's state has neither key
(`backend.fkRd_abs`). -/
def bkNoCmp (γB : backend.BNames) : IProp GF := backend.fkOwn γB 0

/-- The same for mvcc's assumed backend (`kb = none`, the store's own ghost map `γb`): opaque,
given by that backend's creator with its fresh key bucket (no caller in this repository). -/
opaque viewNoCmp (γb : GName) : IProp GF

/-- **The backend of the instance `kb` records no compaction** (`bkNoCmp`, `viewNoCmp`): what
`restore` consumes in place of the opaque premise `backendNoCompaction` (D22 S-g). -/
def kbNoCmp (kb : Option KBReal) (γb : GName) : IProp GF :=
  match kb with
  | none => viewNoCmp γb
  | some d => bkNoCmp d.γB

/-- **The right to write the compaction keys in the instance `kb`** (the contract's `MW`; the
backend-compaction stage, review round 8, R8-2): for the real backend, the client's half of its
compaction-key flag, at any value (`backend.fkOwn`: a put of a compaction key needs it, `fkPut`);
for mvcc's assumed backend, nothing (decided by the agent: an opaque `viewFk` mirroring the real
backend, `viewNoCmp γb := viewFk γb 0`, would make that instance satisfiable by an honest creator,
but it needs the store to hold the right for its compaction, the wiring step's decision; until
then the assumed instance's `viewNoCmp` has no supplier, so results over it that take `kbNoCmp`
are vacuous, not wrong). -/
def kbMW (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => iprop(∃ f : Nat, backend.fkOwn d.γB f)

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

instance rdCap_persistent (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    Persistent (rdCap Rd Tok) := by
  unfold rdCap; infer_instance

/-- **Two slices read at once under `Tok`** (the backend-compaction stage, 3.5; Draft,
2026-10-28): as `rdCap`, for a pair (the compaction job hashes a key and its value together,
`h.WriteKeyValue(keys[i], values[i])`). -/
def rdCap2 (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) : IProp GF :=
  iprop(□ ∀ (s1 s2 : GoSlice) (b1 b2 : GoString), Rd s1 b1 -∗ Rd s2 b2 -∗ Tok -∗
    ∃ dq1 dq2 : DFrac, s1 ↦*{dq1} b1 ∗ s2 ↦*{dq2} b2 ∗ (s1 ↦*{dq1} b1 -∗ s2 ↦*{dq2} b2 -∗ Tok))

instance rdCap2_persistent (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    Persistent (rdCap2 Rd Tok) := by
  unfold rdCap2; infer_instance

/-- What `UnsafeRange(Key, k, nil, 0)` returns of the bucket `m`: the key and its value if `m`
has `k` (read-only outer slices, the inner ones readable through `Rd`), else no key and no
value. -/
def keyVals (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice) (m : Bucket) (k : GoString) :
    IProp GF :=
  match m.lookup k with
  | some v => iprop(∃ (ksl vsl : GoSlice), ks ↦*□ [ksl] ∗ □ Rd ksl k ∗ vs ↦*□ [vsl] ∗ □ Rd vsl v)
  | none => iprop(ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice))

instance keyVals_persistent (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice) (m : Bucket)
    (k : GoString) : Persistent (keyVals Rd ks vs m k) := by
  unfold keyVals; split <;> infer_instance

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

instance pairVals_persistent (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice)
    (l : List (GoString × GoString)) : Persistent (pairVals Rd ks vs l) := by
  unfold pairVals; infer_instance

/-- What `UnsafeRange(Key, lo, hi, 0)` returns of the bucket `m` (`hi` not empty): the entries
with a key in `[klo, khi)`, in key order (`bucketRange`; no limit). -/
def rangeVals (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice) (m : Bucket)
    (klo khi : GoString) : IProp GF :=
  pairVals Rd ks vs (bucketRange m klo khi)

instance rangeVals_persistent (Rd : GoSlice → GoString → IProp GF) (ks vs : GoSlice) (m : Bucket)
    (klo khi : GoString) : Persistent (rangeVals Rd ks vs m klo khi) := by
  unfold rangeVals; infer_instance

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
`issues/etcd-unsafe-range-limit-buffer.md`; all of them with no limit, `keyRangeReadSpec`). -/
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

/-- A value the store writes at a compaction key (`RevToBytes(Revision{Main: x})`, `x ≥ 0`). -/
def metaRevVal (v : GoString) : Prop := ∃ x : w64, 0 ≤ sint.Z x ∧ v = revBytes ⟨x, W64 0⟩ false

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

instance metaReadSpec_persistent (rt : GoInterfaceOk) (nc : Bool)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    Persistent (metaReadSpec (GF := GF) rt nc Rd Tok) := by
  unfold metaReadSpec; infer_instance

/-- A snapshot `m'` of the bucket `m` with some of the keys compaction may delete missing
(`Del`, the store's: `delKey`): the backend's reads after the compaction's `UnsafeDelete`s
(committed or written back) do not see them. -/
def snapThin (m m' : Bucket) (Del : GoString → IProp GF) : IProp GF :=
  iprop(⌜∀ k v, m'.lookup k = some v → m.lookup k = some v⌝ ∗
    □ (∀ k v, ⌜m.lookup k = some v ∧ m'.lookup k = none⌝ -∗ Del k))

instance snapThin_persistent (m m' : Bucket) (Del : GoString → IProp GF) :
    Persistent (snapThin m m' Del) := by
  unfold snapThin; infer_instance

/-- A snapshot with no key missing is thinned (the real backend's snapshots). -/
theorem snapThin_refl (m : Bucket) (Del : GoString → IProp GF) : ⊢ snapThin (GF := GF) m m Del := by
  iunfold snapThin
  isplitl
  · ipureintro; intro k v h; exact h
  iintro !> %k %v %h
  exfalso
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2; cases h2

/-- A `ReadTx` as the compaction's `checkPrevCompactionCompleted` uses it, with no view of the
bucket (it holds neither of the store's locks that hold the view): `RLock` gives a reader's token
`Tok`, under which its reads of the `Meta` bucket's compaction keys (`metaReadSpec`) lend their
slices (`rdCap`), and `RUnlock` takes it (the backend-compaction stage, 2026-10-29: until then
`RLock`/`RUnlock` at `True` and the reads at no token, which the real backend cannot meet). -/
def metaReadTx (rt : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); ∃ (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF), Tok ∗ rdCap Rd Tok ∗
        □ metaReadSpec rt false Rd Tok ∗
        □ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); True }}) }}))

instance metaReadTx_persistent (rt : GoInterfaceOk) : Persistent (metaReadTx (GF := GF) rt) := by
  unfold metaReadTx; infer_instance

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
`issues/etcd-backend-read-buffer-cache-stale-after-commit.md`.) -/
def keyReadLocked (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) : IProp GF :=
  iprop(□ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) ∗
    □ keyRangeSpec rt m Rd Tok ∗
    (if rng then iprop(□ keyRangeReadSpec rt m Rd Tok ∗ □ keyRangeLimSpec rt m Rd Tok cl ∗
      □ rdSplit rt m Rd Tok cl ∗ □ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok))
     else iprop(True)) ∗
    rdCap Rd Tok)

instance keyReadLocked_persistent (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool) :
    Persistent (keyReadLocked RT NC rng rt m Rd Tok cl) := by
  unfold keyReadLocked; cases rng <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- A locked snapshot with its range read has it. -/
theorem keyReadLocked_range (RT NC : IProp GF) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLocked (GF := GF) RT NC true rt m Rd Tok cl ⊢ □ keyRangeReadSpec rt m Rd Tok := by
  unfold keyReadLocked
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨#H, -⟩, -⟩
  iexact H

/-- A locked snapshot with its range read has the limited one (the restore plan's R4b). -/
theorem keyReadLocked_rangeLim (RT NC : IProp GF) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLocked (GF := GF) RT NC true rt m Rd Tok cl ⊢ □ keyRangeLimSpec rt m Rd Tok cl := by
  unfold keyReadLocked
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨-, #H, -⟩, -⟩
  iexact H

/-- A locked snapshot with its range read splits its token (R5b). -/
theorem keyReadLocked_split (RT NC : IProp GF) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLocked (GF := GF) RT NC true rt m Rd Tok cl ⊢ □ rdSplit rt m Rd Tok cl := by
  unfold keyReadLocked
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨-, -, #H, -⟩, -⟩
  iexact H

/-- **A locked snapshot with its range read, of a backend that records no compaction**, finds
none (the backend-compaction stage, 2026-10-29: in place of the axiom `kbNoCmp_metaNone`). -/
theorem keyReadLocked_meta (RT NC : IProp GF) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLocked (GF := GF) RT NC true rt m Rd Tok cl ⊢
      □ (NC -∗ NC ∗ □ metaReadSpec rt true Rd Tok) := by
  unfold keyReadLocked
  simp only [↓reduceIte]
  iintro ⟨-, -, ⟨-, -, -, #H⟩, -⟩
  iexact H

/-- A locked snapshot's slices are readable under its token. -/
theorem keyReadLocked_cap (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (cl : Bool := false) :
    keyReadLocked (GF := GF) RT NC rng rt m Rd Tok cl ⊢ rdCap Rd Tok := by
  unfold keyReadLocked
  iintro ⟨-, -, -, #H⟩
  iexact H

/-- A locked snapshot with its range read is one without (at any `NC`: it matters only with the
range read). -/
theorem keyReadLocked_weaken (RT NC NC' : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    keyReadLocked (GF := GF) RT NC rng rt m Rd Tok ⊢ keyReadLocked RT NC' false rt m Rd Tok := by
  unfold keyReadLocked
  iintro ⟨#H1, #H2, -, #H4⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe H1 H2 H4

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

instance keyReadSnap_persistent (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    Persistent (keyReadSnap View RT NC Del rng rt m L) := by
  unfold keyReadSnap; infer_instance

/-- **A read transaction over a clean read buffer** (the restore plan's R5a): `RLock` gives the
bucket `m` itself (no key missing) with the limited range's prefix clause (`cl`). -/
def keyReadSnapC (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) (rt : GoInterfaceOk) (m : Bucket)
    (L : IProp GF) : IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ keyReadLocked RT NC true rt m Rd Tok true }}))

instance keyReadSnapC_persistent (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    Persistent (keyReadSnapC View RT NC rt m L) := by
  unfold keyReadSnapC; infer_instance

/-- **A reader of the bucket `m` but for keys compaction may have deleted** (2026-10-13, unit 6a):
as `keyReader`, but a key's read may find nothing, for a key compaction may delete (`Del k`): a
thinned snapshot of `m` (`keyReadLocked_readerD`), or the batch transaction under its lock
(`batchTx_readerD`). What `rangeKeys` takes: a read at or above the compaction revision names no
key compaction deleted (`rangeAnswers_not_del`). -/
def keyReaderD (rt : GoInterfaceOk) (m : Bucket) (R : IProp GF) (Del : GoString → IProp GF) :
    IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ R ∗ key ↦*{dq} k }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); ∃ (Rd : GoSlice → GoString → IProp GF)
        (T : IProp GF), T ∗ (T -∗ R) ∗ rdCap Rd T ∗ key ↦*{dq} k ∗
        (keyVals Rd ks vs m k ∨
          (Del k ∗ ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice))) }})

instance keyReaderD_persistent (rt : GoInterfaceOk) (m : Bucket) (R : IProp GF)
    (Del : GoString → IProp GF) : Persistent (keyReaderD (GF := GF) rt m R Del) := by
  unfold keyReaderD; infer_instance

/-- **A locked thinned snapshot is a reader of the bucket it thins**, but for the keys it misses
(deletable). -/
theorem keyReadLocked_readerD (RT NC : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m m' : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) (Del : GoString → IProp GF) :
    keyReadLocked (GF := GF) RT NC rng rt m' Rd Tok ∗ snapThin m m' Del ⊢ keyReaderD rt m Tok Del := by
  iintro ⟨#H, #Ht⟩
  iunfold keyReadLocked at H
  icases H with ⟨-, #Hr, -, #Hcap⟩
  iunfold keyRangeSpec at Hr
  iunfold snapThin at Ht
  icases Ht with ⟨%Hsub, #Hdel⟩
  iunfold keyReaderD
  iintro %b %key %k %dq !> %Φ ⟨#HK, HT, Hkey⟩ HΦ
  iapply Hr $$ %b %key %k %dq %Φ [HT Hkey]
  · iframe HT Hkey; iexact HK
  inext
  iintro %ks %vs ⟨HT, Hkey, #Hkv⟩
  iapply HΦ
  iexists Rd, Tok
  iframe HT Hkey Hcap
  isplitr
  · iintro H; iexact H
  have hkv : ∀ (m1 m2 : Bucket), m1.lookup k = m2.lookup k →
      keyVals (GF := GF) Rd ks vs m1 k = keyVals Rd ks vs m2 k := by
    intro m1 m2 h; unfold keyVals; rw [h]
  cases hm' : m'.lookup k with
  | some v =>
    ileft
    rw [hkv m m' (by rw [Hsub k v hm', hm'])]
    iexact Hkv
  | none =>
    cases hm : m.lookup k with
    | none =>
      ileft
      rw [hkv m m' (by rw [hm, hm'])]
      iexact Hkv
    | some v =>
      iright
      ihave ⟨#Hks, #Hvs⟩ : iprop(ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) $$ [Hkv]
      · have : keyVals (GF := GF) Rd ks vs m' k =
            iprop(ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) := by
          unfold keyVals; rw [hm']
        rw [← this]; iexact Hkv
      iframe Hks Hvs
      iapply Hdel $$ %k %v
      ipureintro; exact ⟨hm, hm'⟩

/-- What a reader of the index knows makes its log well formed and bounded (kept). -/
theorem idxKnows_wf (γ : IdxNames) (kn : IdxKnow) :
    idxKnows (GF := GF) γ kn ⊢ idxKnows γ kn ∗
      ⌜LogWf' kn.log ∧ kn.log.length < 2 ^ 63 ∧ ∀ cs ∈ kn.log, cs.length < 2 ^ 63⌝ := by
  cases kn with
  | cert log =>
    rw [idxKnows_cert]
    iintro #H
    iframe H
    icases H with ⟨#H, -⟩
    iunfold idxCert at H
    icases H with ⟨-, %Hc, -⟩
    ipureintro; exact Hc
  | writer ilog pend =>
    rw [idxKnows_writer]
    iintro H
    ihave %Hw := idxWriter_wf γ ilog pend $$ H
    iframe H
    ipureintro
    obtain ⟨hwf, hlen, hp, hcs⟩ := Hw
    refine ⟨hwf, by simp; omega, ?_⟩
    intro cs hcs'
    rcases List.mem_append.1 hcs' with h | h
    · exact hcs cs h
    · rw [List.mem_singleton] at h; rw [h]; exact hp

/-! ## The post-lock hook -/

/-- The real backend's post-lock hook is the Go function `f` for good (`plHookRO`), not `nil`. -/
def bkHookIs (γB : backend.BNames) (f : val) : IProp GF :=
  iprop(∃ g : GoFunc, ⌜f = #g ∧ g ≠ func.nil⌝ ∗ backend.plHookRO γB g)

instance bkHookIs_persistent (γB : backend.BNames) (f : val) :
    Persistent (bkHookIs (GF := GF) γB f) := by
  unfold bkHookIs; infer_instance

/-- **The post-lock hook is `f` for good** in the backend instance `kb` (persistent; unit N4,
D14b): for mvcc's assumed backend, the store's own read-only ghost variable `hfn` (`NewStore`
allocates it at its caller's `f`); for the real backend, the backend's own slot frozen at the Go
function `f` (`backend.plHookRO`: the etcd server installs the hook after creating the store,
`server.go:412`, and freezes it then), not `nil`. -/
def kbHookIs (kb : Option KBReal) (hfn : GName) (f : val) : IProp GF :=
  match kb with
  | none => dghostVar hfn DFrac.discard f
  | some d => bkHookIs d.γB f

instance kbHookIs_persistent (kb : Option KBReal) (hfn : GName) (f : val) :
    Persistent (kbHookIs (GF := GF) kb hfn f) := by
  unfold kbHookIs; split <;> infer_instance

/-- The store's post-lock hook fact, as a predicate of the hook (`batchTxSpecG`'s `HF`). -/
abbrev hookFn (γ : StoreNames) : val → IProp GF := kbHookIs γ.kb γ.hookFn

/-- Two facts of the hook agree. -/
theorem kbHookIs_agree (kb : Option KBReal) (hfn : GName) (f f' : val) :
    kbHookIs (GF := GF) kb hfn f ∗ kbHookIs kb hfn f' ⊢ ⌜f = f'⌝ := by
  unfold kbHookIs
  cases kb with
  | none =>
    iintro ⟨H1, H2⟩
    iapply dghostVar_agree hfn f DFrac.discard f' DFrac.discard $$ H1 H2
  | some d =>
    unfold bkHookIs
    iintro ⟨⟨%g, %hg, H1⟩, ⟨%g', %hg', H2⟩⟩
    have hag : backend.plHookRO (GF := GF) d.γB g ∗ backend.plHookRO d.γB g' ⊢ ⌜g = g'⌝ := by
      unfold backend.plHookRO backend.plHookAt
      iintro ⟨H1, H2⟩
      iapply dghostVar_agree d.γB.hook g DFrac.discard g' DFrac.discard $$ H1 H2
    ihave %Hg := hag $$ [$H1 $H2]
    ipureintro; rw [hg.1, hg'.1, Hg]

/-- **The batch lock's invariant** `P` of the store (persistent; a saved proposition, so that a
caller naming it agrees with the store's). -/
def hookP (γ : StoreNames) (P : IProp GF) : IProp GF := savedPropOwn γ.hook DFrac.discard P

instance hookP_persistent (γ : StoreNames) (P : IProp GF) : Persistent (hookP γ P) := by
  unfold hookP; infer_instance

/-- **The post-lock hook of the store's names** (persistent): the backend's batch lock has invariant
`P` and its `LockInsideApply` runs the hook `f` (a Go `func()`) right after taking the lock
(`batchTx.LockInsideApply` calls `txPostLockInsideApplyHook`). `P` is fixed per batch lock
(`NewStore` allocates its name); the hook is `f` for good (`kbHookIs`: for the real backend, the
backend's slot, frozen when the server installs it; unit N4, D14b), so that a caller naming them
agrees with the store's (`hookOk_agree`, `hookOk_agree_lc`). Facts of the names `γ`, true for
good (D22 receiver epochs, S5b: until then `hookIs`). -/
def hookOk (γ : StoreNames) (P : IProp GF) (f : val) : IProp GF :=
  iprop(hookP γ P ∗ hookFn γ f)

instance hookOk_persistent (γ : StoreNames) (P : IProp GF) (f : val) :
    Persistent (hookOk γ P f) := by
  unfold hookOk; infer_instance

/-- **The store's post-lock hook, for its sole writer** (D22 receiver epochs, S5b: not persistent):
the hook's facts at the names `γ` (`hookOk`) and the writer's fragment (`writerFrag`: the names
`γ` are the store's current ones). `store.Write` takes it and gives it back; a write transaction's
`End` gives the fragment back (`txnEndPost`). -/
def hookIs (γ : StoreNames) (P : IProp GF) (f : val) : IProp GF :=
  iprop(hookOk γ P f ∗ writerFrag γ)

/-- The writer's hook, its facts and its fragment. -/
theorem hookIs_split (γ : StoreNames) (P : IProp GF) (f : val) :
    hookIs (GF := GF) γ P f ⊣⊢ hookOk γ P f ∗ writerFrag γ := by
  unfold hookIs; exact .rfl

/-- Two views of the hook agree: the same function, the same invariant a step later. -/
theorem hookOk_agree (γ : StoreNames) (P P' : IProp GF) (f f' : val) :
    hookOk γ P f ∗ hookOk γ P' f' ⊢ ⌜f = f'⌝ ∗ ▷ (P ≡ P') := by
  iintro ⟨H1, H2⟩
  iunfold hookOk at H1 H2
  icases H1 with ⟨HP1, Hf1⟩
  icases H2 with ⟨HP2, Hf2⟩
  ihave %Hf := kbHookIs_agree γ.kb γ.hookFn f f' $$ [$Hf1 $Hf2]
  iunfold hookP at HP1 HP2
  ihave Heq := saved_prop_agree γ.hook DFrac.discard DFrac.discard P P' $$ HP1 HP2
  iframe Heq
  ipureintro; exact Hf

/-- **What `NewStore` records of the hook** (persistent): the batch lock's invariant `P`, and for
mvcc's assumed backend the hook `f` (its own slot, frozen); for the real backend nothing of the
hook, which the etcd server installs later (`hookIs_of_init`; unit N4, D14b). -/
def hookInit (γ : StoreNames) (P : IProp GF) (f : val) : IProp GF :=
  iprop(hookP γ P ∗ match γ.kb with
    | none => hookFn γ f
    | some _ => iprop(True))

instance hookInit_persistent (γ : StoreNames) (P : IProp GF) (f : val) :
    Persistent (hookInit γ P f) := by
  unfold hookInit; split <;> infer_instance

/-- **The hook installed for good** (`plHookRO`, after `SetTxPostLockInsideApplyHook`): over the
real backend, the recorded invariant and the frozen hook `g` are the store's hook. -/
theorem hookOk_of_init (γ : StoreNames) (P : IProp GF) (f : val) (d : KBReal) (h : γ.kb = some d)
    (g : GoFunc) (hg : g ≠ func.nil) :
    hookInit (GF := GF) γ P f ∗ backend.plHookRO d.γB g ⊢ hookOk γ P #g := by
  unfold hookInit hookOk hookFn kbHookIs bkHookIs
  rw [h]
  iintro ⟨⟨#HP, -⟩, #Hg⟩
  iframe HP
  iexists g
  iframe Hg
  ipureintro; exact ⟨rfl, hg⟩

/-- `hookOk_of_init`, with the writer's fragment (S5b). -/
theorem hookIs_of_init (γ : StoreNames) (P : IProp GF) (f : val) (d : KBReal) (h : γ.kb = some d)
    (g : GoFunc) (hg : g ≠ func.nil) :
    hookInit (GF := GF) γ P f ∗ backend.plHookRO d.γB g ∗ writerFrag γ ⊢ hookIs γ P #g := by
  iintro ⟨#Hi, #Hg, Hf⟩
  iunfold hookIs
  iframe Hf
  iapply hookOk_of_init γ P f d h g hg
  iframe Hi Hg

/-- **The critical-section contract** of a writing call under the store's batch lock with
invariant `P` and post-lock hook `f` (the shape of the server's `apply.Apply` contract): the
caller's `Pre`, the hook's triple from it (`{P ∗ Pre} f() {Q}`, run by `LockInsideApply`), and
the caller's update `Q ={⊤}=∗ P ∗ Post`, applied after the writes, before `Unlock` (which
takes `P` back). The call returns `Post` if it took the lock, else `Pre`. -/
def csContract (P : IProp GF) (f : val) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
    (Q ={⊤}=∗ P ∗ Post))

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

instance unlockAt_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (W P U : IProp GF) (l : Puts) : Persistent (unlockAt bt View W P U l) := by
  unfold unlockAt; infer_instance

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
def metaPutCap (bt : GoInterfaceOk) (X Y : IProp GF) : IProp GF :=
  iprop(□ ∀ (b : GoInterface) (key val : GoSlice) (k v : GoString),
    ⌜metaCompactKey k ∧ metaRevVal v⌝ →
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ X ∗ key ↦*□ k ∗
        val ↦*□ v }}
      (App (App (App (Val #(methods bt.ty go!"UnsafePut" bt.v)) (Val #b)) (Val #key)) (Val #val))
    {{ RET #(); Y }})

instance metaPutCap_persistent (bt : GoInterfaceOk) (X Y : IProp GF) :
    Persistent (metaPutCap (GF := GF) bt X Y) := by
  unfold metaPutCap; infer_instance

/-- **The limited range's batch bound** (the backend-compaction stage, decision O3; review round 2,
R2-3): a compacting range reads at most `2^56` entries, so the session it ends (`limit` deletes and
one `Meta` put after a start below the backend's `P.limit ≤ 2^57`) stays within the backend's count
(`pend + hookMax < 2^58`). The job reads `CompactionBatchLimit` entries: the store's scope premise
(`isStore`'s `Hcfgl`; Go has no such bound). -/
abbrev rangeLimitMax : Int := 2 ^ 56

/-- **The store's batch limit** (the configuration's `CompactionBatchLimit`; `NewStore`'s premise): not
negative (`issues/etcd-compaction-negative-batch-limit.md`: `NewStore` replaces `0` by the default,
and a negative one makes the job's loop run forever: its range then reads nothing and the
loop never reaches its end condition), and at most `rangeLimitMax` (the
backend-compaction stage's scope premise, decision O3 and review round 2: the job's range then
stays within the backend's count; Go has no such bound, so it is a restriction of the configuration
the results cover, `notes/decisions.md`). -/
def batchLimitOk (x : w64) : Prop := 0 ≤ sint.Z x ∧ sint.Z x ≤ rangeLimitMax

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
`Unlock` takes any `U n`. A `Meta` put on its own (`metaPutCap`) goes from `Locked []` to such a
token. The store's record of the meta keys is its own (`metaCompact`).

**The lessor's delete** (leases T3, 2026-10-25; `notes/leases-plan.md`): `lessor.Revoke` deletes
the lease's record from the `Lease` bucket under the lock of the KV write transaction its range
deleter opened (`UnsafeDelete(schema.Lease, k)`, the store's batch transaction's), with the right
`Rb r` to write the tracked buckets `r` (the real backend's client half of them, `rbOwn`; the
bucket is tracked, D22), given back as `Rb (rbDel r leaseName k)`. The lock's token becomes one
that only `Unlock` takes (`unlockAt`, at the same puts): the backend counts its pending
operations, and the store makes no other call after it (`Revoke` ends the transaction).

The store's instance over mvcc's assumed backend (`batchTxSpec`) has no tokens (`RT = WT =
True`), no condition and `Cmp`: the backend's bridge (`BackendBridge.lean`) proves the general
one with the backend's, `Cmp` false (2026-10-13, unit 4; the merge with the compaction). -/
def batchTxSpecG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF) (P : IProp GF)
    (HF : val → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (MW : IProp GF) :
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
        (klo khi : GoString) (limit : w64) (dqlo dqhi : DFrac),
      ⌜0 < sint.Z limit ∧ sint.Z limit ≤ rangeLimitMax ∧ khi ≠ []⌝ →
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked [] ∗ View q m ∗
          lo ↦*{dqlo} klo ∗ hi ↦*{dqhi} khi }}
        (App (App (App (App (Val #(methods bt.ty go!"UnsafeRange" bt.v)) (Val #b)) (Val #lo))
          (Val #hi)) (Val #limit))
      {{ (ks vs : GoSlice), RET (PairV #ks #vs); View q m ∗ lo ↦*{dqlo} klo ∗
          hi ↦*{dqhi} khi ∗
          ∃ (m' : Bucket) (Rd : GoSlice → GoString → IProp GF) (U : Nat → IProp GF),
            U ((sint.Z limit).toNat + 1) ∗
            snapThin m m' Del ∗
            (□ ∀ n : Nat, rdCap Rd (U n)) ∗ (□ ∀ n : Nat, rdCap2 Rd (U n)) ∗
            pairVals Rd ks vs ((bucketRange m' klo khi).take (sint.Z limit).toNat) ∗
            □ (∀ (key : GoSlice) (k : GoString) (n : Nat),
              {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ U (n + 1) ∗
                  Del k ∗ □ Rd key k }}
                (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key))
              {{ RET #(); U n }}) ∗
            (□ ∀ n : Nat, metaPutCap bt iprop(U (n + 1) ∗ MW) iprop(U n ∗ MW)) ∗
            □ (∀ n : Nat, {{ U n ∗ W ∗ P }} (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
                {{ RET #(); True }}) }}) ∗
    -- (R2-3) a compaction key put into `Meta` in a fresh session (`SetScheduledCompact`'s) ends
    -- it in a token only `Unlock` takes, as the lessor's delete does; with the right `MW` to write
    -- the compaction keys, given back (the real backend's client half of its compaction-key flag,
    -- `backend.fkOwn`: the backend-compaction stage, 2026-10-29; `True` for mvcc's assumed backend)
    □ (⌜Cmp⌝ -∗ metaPutCap bt iprop(Locked [] ∗ MW)
      iprop((∃ U : IProp GF, U ∗ unlockAt bt View W P U []) ∗ MW)) ∗
    □ (∀ (l : Puts) (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac)
        (r : GMap GoString backend.BktData),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b ∗ Locked l ∗
          key ↦*{dq} k ∗ Rb r }}
        (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key))
      {{ RET #(); (∃ U : IProp GF, U ∗ unlockAt bt View W P U l) ∗ key ↦*{dq} k ∗
          Rb (rbDel r leaseName k) }}))

instance batchTxSpecG_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF)
    (P : IProp GF) (HF : val → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (MW : IProp GF) :
    Persistent (batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW) := by
  unfold batchTxSpecG; infer_instance

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

instance batchTxInitSpec_persistent (bt : GoInterfaceOk) (RT WT : IProp GF) (W Wi Dep : IProp GF)
    (LockedO : Nat → IProp GF) (P : IProp GF) :
    Persistent (batchTxInitSpec bt RT WT W Wi Dep LockedO P) := by
  unfold batchTxInitSpec; infer_instance

/-- `bt` is a batch transaction (its lock tokens' predicates are its own). -/
def isBatchTxG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (Bt : GoInterfaceOk → IProp GF := fun _ => iprop(True)) (MW : IProp GF) :
    IProp GF :=
  iprop(∃ (Locked : Puts → IProp GF) (LockedO : Nat → IProp GF),
    batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW ∗
      batchTxInitSpec bt RT WT W Wi Dep LockedO P ∗ □ Bt bt)

instance isBatchTxG_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF) (MW : IProp GF) :
    Persistent (isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW) := by
  unfold isBatchTxG; infer_instance

/-- No condition on the puts (mvcc's assumed backend). -/
def noPutCond : Bucket → Puts → GoString → GoString → Prop := fun _ _ _ _ => True

/-- **The real backend's condition on a put** (`BackendBridge.lean`): at most `2^56` puts in a
session (the backend's bound on a session's operations), a key of `1..MaxKeySize` bytes above
every key of the bucket `m` and of the session's puts `l` (the safe-range discipline of the
`Key` bucket, and `UnsafeSeqPut`'s order check). (No bound on the value: bbolt refuses one above
`MaxValueSize` and the backend's `lg.Fatal` exits:
`issues/etcd-backend-put-value-too-large-fatal.md`.) -/
def keyPutOk (m : Bucket) (l : Puts) (k _v : GoString) : Prop :=
  l.length < 2 ^ 56 ∧ 0 < k.length ∧ k.length ≤ backend.maxKeySize ∧
    (∀ k' v', m.lookup k' = some v' → go.GoStringLt k' k) ∧ ∀ p ∈ l, go.GoStringLt p.1 k

/-- The store's batch transaction contract over mvcc's assumed backend: no tokens, no condition
on the puts, the compaction's calls. -/
def batchTxSpec (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF) (HF : val → IProp GF) : IProp GF :=
  batchTxSpecG bt View iprop(True) iprop(True) noPutCond Del W Dep True Locked P HF (MW := kbMW none)

instance batchTxSpec_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF)
    (HF : val → IProp GF) : Persistent (batchTxSpec bt View Del W Dep Locked P HF) := by
  unfold batchTxSpec; infer_instance

/-- **The batch transaction under its lock is a reader of its own puts over the view**, but for
the keys compaction may have deleted (2026-10-13, unit 6a: `batchTx_reader` without its "nothing
deletable" premise). -/
theorem batchTx_readerD (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (MW : IProp GF) (l : Puts) (q : Qp) (m : Bucket) :
    batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW ⊢
      keyReaderD bt (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) iprop(Locked l ∗ View q m) Del := by
  iintro #H
  iunfold batchTxSpecG at H
  icases H with ⟨-, -, -, -, #Hr, -⟩
  iunfold keyReaderD
  iintro %b %key %k %dq !> %Φ ⟨#HK, ⟨Hl, Hv⟩, Hkey⟩ HΦ
  iapply Hr $$ %l %q %m %b %key %k %dq [Hl Hv Hkey]
  · iframe Hl Hv Hkey; iexact HK
  inext
  iintro %ks %vs ⟨%Rd, %T, HT, Hback, #Hcap, Hv, Hkey, Hkv⟩
  iapply HΦ
  iexists Rd, iprop(T ∗ View q m)
  iframe HT Hv Hkey Hkv
  isplitl [Hback]
  · iintro ⟨HT, Hv⟩
    ihave Hl := Hback $$ HT
    iframe Hl Hv
  iunfold rdCap at Hcap
  iunfold rdCap
  iintro !> %s %bs HRd ⟨HT, Hv⟩
  icases Hcap $$ %s %bs HRd HT with ⟨%dq', Hs, Hb⟩
  iexists dq'
  iframe Hs
  iintro Hs
  ihave HT := Hb $$ Hs
  iframe HT Hv

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
(`metaReadTx`: `checkPrevCompactionCompleted`). The instance of mvcc's assumed backend
(`isKeyBackend`) has no tokens, no condition on the puts (`batchTxSpecG`'s `PutOk`) and `Cmp`;
`BackendBridge.lean` proves the general one of the backend, `Cmp` false (2026-10-13, unit 4; the
merge with the compaction, unit 5a). -/
def isKeyBackendG (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF := fun X Y => iprop(□ (X -∗ Y)))
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True))
    (Bt : GoInterfaceOk → IProp GF := fun _ => iprop(True))
    (SR SRh : IProp GF := iprop(True)) (MW : IProp GF) :
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
          isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW }}) ∗
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
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); metaReadTx rt }})))

instance isKeyBackendG_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT NC : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (SR SRh MW : IProp GF) :
    Persistent (isKeyBackendG b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW) := by
  unfold isKeyBackendG; infer_instance

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
          ⌜∀ it ∈ l, I.lookup it = none ∨ I.lookup it = some id⌝ ∗ items ↦*{dq} l }}
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

instance isLessor_persistent (le : GoInterface) (γl : GName) : Persistent (isLessor (GF := GF) le γl) := by
  unfold isLessor; infer_instance

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

/-- mvcc's view of the `Key` bucket over the real backend with the read buffer known clean
(`backend.bViewC … true`, the restore plan's R5a). -/
def bkViewC (γB : backend.BNames) (q : Qp) (m : Bucket) : IProp GF :=
  iprop(∃ vd : backend.VData, backend.bViewC γB q vd true ∗ ⌜keyView vd m⌝)

/-- The view of the bucket in the instance `kb` with the read buffer known clean (the model's:
its view). -/
def kbViewC (kb : Option KBReal) (γb : GName) (q : Qp) (m : Bucket) : IProp GF :=
  match kb with
  | none => ghostMapAuth γb q m
  | some d => bkViewC d.γB q m

theorem kbViewC_kbView (kb : Option KBReal) (γb : GName) (q : Qp) (m : Bucket) :
    kbViewC (GF := GF) kb γb q m ⊢ kbView kb γb q m := by
  cases kb with
  | none => unfold kbViewC kbView; iintro H; iexact H
  | some d =>
    unfold kbViewC kbView bkViewC bkView
    iintro ⟨%vd, Hv, %Hk⟩
    iexists vd
    iframe %Hk
    iapply backend.bViewC_bView $$ Hv

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

/-- **The write-back tokens' supply** in the instance `kb` (3.4, decision O4; revised after review
round 2, R2-7, the user's: **one stock**): for the real backend, a write session's token for each
time receipt, so that the compaction job, whose batches are not bounded in advance, pays each
batch's `Unlock` and `ForceCommit` from the steps it takes. The tokens come from the same
receipt-funded stock as the server's `srvWTPool` (D22's: `InvApplier.lean`, an invariant holding
`⧗ a ∗ ownToks γB.wb n` with `receiptBound ≤ a + n + 1`), not from a pool of the job's own: both
pools would each need about `receiptBound` of the backend's `wbInit = 2^40 - 1`, and D22 already
takes nearly all of it (`receiptBound ≤ wbInit - 6`); one stock suffices since every step yields one
receipt, whoever takes it. `NewServer` (the wiring step) gives this persistent conversion from
`srvWTPool`'s invariant at the boot backend `d`: valid because the configuration with the compactor
on installs no snapshot (`notes/m2-plan.md`, "no restore in compaction mode"), so `s.be` stays `d`.
What it needs of D22's statements (listed, not changed yet): `srvWTPool`'s invariant exposing the
receipt-to-token conversion at the boot backend when the compactor is on, and `wbInit`'s split
(`receiptBound ≤ wbInit - 6` covers both, since they share it) made explicit there. -/
def kbWTSupply (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => iprop(□ (⧗ 1 ={⊤}=∗ backend.wbTok d.γB))

/-- **The compaction job's budgets** in the instance `kb` (3.4): a reader's token (its batches'
`LockOutsideApply` lend it), the safe-range slot, and the write-back supply; exclusive, handed from
job to job (to be carried in the compaction token, `compactTok`, when the stores switch to the new
bridge: the stage's next Draft step, with `NewStore`'s callers supplying it). All `True` for mvcc's
assumed backend. -/
def compactJobRes (kb : Option KBReal) : IProp GF :=
  iprop(kbRT kb ∗ kbSR kb ∗ kbWTSupply kb)

/-- **The real backend's commit requests** (D22 the stored-index window, 2026-10-23): a plain wand,
or a request its hooks serve (`backend.commitReq`) for some batch-lock and hooks' resources of
the backend. -/
def bkReq (γB : backend.BNames) (P : backend.BParams) (b : Loc) (X Y : IProp GF) : IProp GF :=
  iprop(□ (X -∗ Y) ∨ ∃ W Pk : IProp GF, backend.isBackend γB P W Pk b ∗
    backend.commitReq γB P Pk b X Y)

instance bkReq_persistent (γB : backend.BNames) (P : backend.BParams) (b : Loc) (X Y : IProp GF) :
    Persistent (bkReq γB P b X Y) := by
  unfold bkReq; infer_instance

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

/-- The bound on a write transaction's changes in the instance `kb` (`2^63`; `2^56` for the
real backend: its bound on a session's puts). -/
def kbPutMax (kb : Option KBReal) : Nat :=
  match kb with
  | none => 2 ^ 63
  | some _ => 2 ^ 56

theorem kbPutMax_le (kb : Option KBReal) : kbPutMax kb ≤ 2 ^ 63 := by
  cases kb <;> simp [kbPutMax]

/-- The store's view of the bucket (`kbView` of its instance). -/
def bucketView (γ : StoreNames) (q : Qp) (m : Bucket) : IProp GF := kbView γ.kb γ.bucket q m

/-- The store's view of its bucket with the backend's read buffer known clean (the restore plan's
R5a). -/
def bucketViewC (γ : StoreNames) (q : Qp) (m : Bucket) : IProp GF := kbViewC γ.kb γ.bucket q m

theorem bucketViewC_bucketView (γ : StoreNames) (q : Qp) (m : Bucket) :
    bucketViewC (GF := GF) γ q m ⊢ bucketView γ q m :=
  kbViewC_kbView γ.kb γ.bucket q m

/-- The store's reader token (`kbRT`). -/
abbrev storeRT (γ : StoreNames) : IProp GF := kbRT γ.kb

/-- The store's write token (`kbWT`): `store.Write` spends one. -/
abbrev storeWT (γ : StoreNames) : IProp GF := kbWT γ.kb

/-- The store's backend's commit requests (`kbReq`). -/
abbrev storeReq (γ : StoreNames) : IProp GF → IProp GF → IProp GF := kbReq γ.kb

instance kbReq_persistent (kb : Option KBReal) (X Y : IProp GF) :
    Persistent (kbReq (GF := GF) kb X Y) := by
  unfold kbReq; cases kb <;> dsimp only <;> infer_instance

/-- A plain wand is a request every instance serves. -/
theorem storeReq_of_wand (γ : StoreNames) (X Y : IProp GF) :
    □ (X -∗ Y) ⊢ storeReq (GF := GF) γ X Y := by
  unfold storeReq kbReq
  cases γ.kb with
  | none => iintro #H; iexact H
  | some d => unfold bkReq; iintro #H; ileft; iexact H

/-- No request. -/
theorem storeReq_true (γ : StoreNames) : ⊢ storeReq (GF := GF) γ iprop(True) iprop(True) := by
  iapply storeReq_of_wand
  iintro !> -
  itrivial

/-- **A backend contract serving the store's requests serves plain wands** (`isKeyBackendG`'s
default `Req`; D22 the stored-index window, 2026-10-23): what the callers that ask nothing of a
commit take. -/
theorem isKeyBackendG_wand {b : GoInterface} {View : Qp → Bucket → IProp GF} {RT WT NC : IProp GF}
    {PutOk : Bucket → Puts → GoString → GoString → Prop} {Del : GoString → IProp GF}
    {W Wi Dep : IProp GF} {Cmp : Prop} {P : IProp GF} {HF : val → IProp GF} {γ : StoreNames}
    {Rb : GMap GoString backend.BktData → IProp GF} {Bt : GoInterfaceOk → IProp GF} {MW : IProp GF} :
    isKeyBackendG (GF := GF) b View RT WT NC PutOk Del W Wi Dep Cmp P HF (storeReq γ) Rb Bt
        (MW := MW) ⊢
      isKeyBackendG b View RT WT NC PutOk Del W Wi Dep Cmp P HF (Rb := Rb) (Bt := Bt) (MW := MW) := by
  iintro #H
  unfold isKeyBackendG
  icases H with ⟨%bi, %Hbi, #H1, #H2, #H3, #HFc, #H5, #H6, #H7⟩
  iexists bi
  iframe H1 H2 H3 H5 H6 H7
  isplitr
  · ipureintro; exact Hbi
  iintro !> %X %Y %Φ !> ⟨Hrt, Hwt, HX, #Hw⟩ HΦ
  iapply HFc $$ %X %Y [Hrt Hwt HX] HΦ
  iframe Hrt Hwt HX
  iapply storeReq_of_wand
  iintro !>
  iexact Hw

/-- The store's condition on its backend's puts (`kbPutOk`). -/
abbrev storePutOk (γ : StoreNames) : Bucket → Puts → GoString → GoString → Prop := kbPutOk γ.kb

/-- The store's bound on a write transaction's changes (`kbPutMax`). -/
abbrev putMax (γ : StoreNames) : Nat := kbPutMax γ.kb

theorem putMax_ge (γ : StoreNames) : 2 ^ 56 ≤ putMax γ := by
  unfold putMax kbPutMax; cases γ.kb <;> simp

/-- Whether the backend of the instance `kb` supports mvcc's compaction (`isKeyBackendG`'s
`Cmp`): mvcc's assumed backend does; the real backend does not yet (its model forbids deleting
from the safe-range `Key` bucket, and an `Unlock` that changes what readers see needs the
clients' whole view, which the compaction job, under the batch lock alone, does not hold;
`notes/decisions.md`, "The compaction over the real backend"). The backend-compaction stage
(`notes/backend-cmp-plan.md`, decision O5) makes it `True` once the new bridge
(`isKeyBackendG_of_backendC`) is proved; until then the stores keep the old one. -/
def kbCmp (kb : Option KBReal) : Prop := kb = none

/-- The store's backend supports compaction (`kbCmp`). -/
abbrev storeCmp (γ : StoreNames) : Prop := kbCmp γ.kb

/-- **The right to write the tracked buckets** (`batchTxSpecG`'s `Rb`, at the buckets `r`) of the
instance `kb`: the real backend's client half of them (`backend.rbOwn`, D22), with its parameters
letting the lessor delete from `Lease` (`leaseParams`: the holder knows the table); nothing for
mvcc's assumed backend (leases T3, 2026-10-25: what the lessor's delete in `Revoke` takes). -/
def kbRb : Option KBReal → GMap GoString backend.BktData → IProp GF
  | none => fun _ => iprop(True)
  | some d => fun r => iprop(backend.rbOwn d.γB r ∗ ⌜leaseParams d.P⌝)

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

instance bkBt_persistent (be : Loc) (bt : GoInterfaceOk) : Persistent (bkBt (GF := GF) be bt) := by
  unfold bkBt; infer_instance

/-- **The batch transaction `bt` is the backend's** (`isKeyBackendG`'s `Bt`; leases T3, L2d (iv),
2026-10-25) for the instance `kb`: over the real backend at `d.be`, its `BatchTx()` returns `bt`
(the backend's `batchTx` field, read-only), so that the lessor's `le.b.BatchTx()` in `Revoke` is
the batch transaction the KV write transaction holds the lock of; nothing over mvcc's assumed
backend. -/
def kbBt : Option KBReal → GoInterfaceOk → IProp GF
  | none => fun _ => iprop(True)
  | some d => bkBt d.be

instance kbBt_persistent (kb : Option KBReal) (bt : GoInterfaceOk) :
    Persistent (kbBt (GF := GF) kb bt) := by
  cases kb <;> unfold kbBt <;> infer_instance

/-- The store's batch transaction is its backend's (`kbBt`). -/
abbrev storeBt (γ : StoreNames) : GoInterfaceOk → IProp GF := kbBt γ.kb

/-- The pending puts are at most the pending changes. -/
theorem pendPuts_length_le (ilog : Log) (pend : List Change) :
    (pendPuts ilog pend).length ≤ pend.length := by
  unfold pendPuts bucketOfRev
  exact Nat.le_trans (List.length_filterMap_le ..) (by simp)

/-- **The store's next put meets its backend's condition**: the key of the pending revision at
the next position, above the bucket's keys and the pending puts' (`RevOrder.lean`). -/
theorem storePutOk_next (γ : StoreNames) (ilog : Log) (pend : List Change) (t : Bool)
    (d : GoString) (hlen : ilog.length < 2 ^ 63) (hcs : ∀ cs ∈ ilog, cs.length < 2 ^ 63)
    (hp : pend.length + 1 < putMax γ) :
    storePutOk γ (bucketMap ilog) (pendPuts ilog pend)
      (revBytes ⟨W64 ilog.length, W64 pend.length⟩ t) d := by
  unfold storePutOk kbPutOk
  unfold putMax kbPutMax at hp
  cases hkb : γ.kb with
  | none => trivial
  | some _ =>
    rw [hkb] at hp
    simp only at hp ⊢
    have hk := RevOrder.revBytes_keyOk ⟨W64 ilog.length, W64 pend.length⟩ t
    refine ⟨by have := pendPuts_length_le ilog pend; omega, hk.1, hk.2, ?_, ?_⟩
    · intro k' v' h
      exact RevOrder.bucketMap_lt_next ilog pend t hlen hcs h
    · intro p hp'
      exact RevOrder.pendPuts_lt_next ilog pend t (by omega) hp'

instance bucketView_fractional (γ : StoreNames) (m : Bucket) :
    Fractional (fun q => bucketView (GF := GF) γ q m) where
  fractional q1 q2 := by
    unfold bucketView kbView
    cases γ.kb with
    | none =>
      exact (ghostMapAuth_fractional (GF := GF) γ.bucket m).fractional q1 q2
    | some d =>
      have hv := fun vd : backend.VData =>
        (ghostVar_fractional (GF := GF) d.γB.view vd).fractional q1.half q2.half
      have hc := (ghostVar_fractional (GF := GF) d.γB.cvw ()).fractional q1.half q2.half
      have hl := fun c : Bool => (ghostVar_fractional (GF := GF) d.γB.cln c).fractional q1.half q2.half
      simp only
      unfold bkView backend.bView backend.bViewC
      rw [Qp_half_add]
      constructor
      · iintro ⟨%vd, ⟨%c, Hv, Hc, Hl⟩, %Hk⟩
        icases (hv vd).1 $$ Hv with ⟨Hv1, Hv2⟩
        icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
        icases (hl c).1 $$ Hl with ⟨Hl1, Hl2⟩
        isplitl [Hv1 Hc1 Hl1]
        · iexists vd; iframe; ipureintro; exact Hk
        · iexists vd; iframe; ipureintro; exact Hk
      · iintro ⟨⟨%vd1, ⟨%c1, Hv1, Hc1, Hl1⟩, %Hk1⟩, ⟨%vd2, ⟨%c2, Hv2, Hc2, Hl2⟩, %Hk2⟩⟩
        ihave %Heq := ghostVar_agree d.γB.view vd1 _ vd2 _ $$ Hv1 Hv2
        ihave %Heqc := ghostVar_agree d.γB.cln c1 _ c2 _ $$ Hl1 Hl2
        subst Heq Heqc
        iexists vd1
        isplitl [Hv1 Hv2 Hc1 Hc2 Hl1 Hl2]
        · iexists c1
          isplitl [Hv1 Hv2]
          · iapply (hv vd1).2; iframe
          isplitl [Hc1 Hc2]
          · iapply hc.2; iframe
          · iapply (hl c1).2; iframe
        ipureintro; exact Hk1

/-- The view as two halves (`s.revMu`'s and the batch lock's). -/
theorem bucketView_halves (γ : StoreNames) (q : Qp) (m : Bucket) :
    bucketView (GF := GF) γ q m ⊣⊢ bucketView γ q.half m ∗ bucketView γ q.half m := by
  have h := (bucketView_fractional (GF := GF) γ m).fractional q.half q.half
  rw [Qp.half_add_half] at h
  exact h

/-- A revision token: the right to open one write transaction (`store.Write`). The store's
`NewStore` hands out `2 ^ 63 - 5` of them: with the budget `writerRes` keeps, the revision
counter stays below `2 ^ 63 - 2`. -/
def revToken (γ : StoreNames) : IProp GF := ownToks γ.revs 1

/-- The revision budget's authority in two parts (`s.revMu`'s and the writer's). -/
theorem ownTokAuthDfrac_split (γr : GName) (dq dq' : DFrac) (n : Nat) :
    ownTokAuthDfrac (GF := GF) γr (dq • dq') n ⊣⊢ ownTokAuthDfrac γr dq n ∗ ownTokAuthDfrac γr dq' n := by
  rw [ownTokAuthDfrac_unseal]
  unfold ownTokAuthDfracDef
  rw [Auth.auth_dfrac_op]
  exact own_op γr _ _

/-- The revision budget's authority as two halves. -/
theorem ownTokAuth_halves (γr : GName) (n : Nat) :
    ownTokAuth (GF := GF) γr n ⊣⊢
      ownTokAuthDfrac γr (DFrac.own (1 : Qp).half) n ∗ ownTokAuthDfrac γr (DFrac.own (1 : Qp).half) n := by
  rw [ownTokAuth, dfrac_own_half_half]
  exact ownTokAuthDfrac_split γr _ _ n

/-! ## Compaction: its revision, what it may delete, the meta keys -/

instance crevUB_timeless (γ : IdxNames) (q : Qp) (c : Int) :
    Timeless (crevUB (GF := GF) γ q c) := by
  unfold crevUB; infer_instance

/-- **The index compactor's token, at or below `c`** (exclusive): the index's compactor token
(`idxCompactor`, `treeIndex.Compact`'s) at the revision of the last compaction of the index, at most
`c` (a compaction job at `c` may find the index compacted below it: an earlier job interrupted
before its pass, by a cancelled context, leaves the token where it was; 2026-10-13, unit 5c). -/
def compactTok (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(∃ c' : Int, ⌜c' ≤ c⌝ ∗ idxCompactor γ.idx c')

/-- The compactor's token is good at any higher revision. -/
theorem compactTok_mono (γ : StoreNames) (c c' : Int) (h : c ≤ c') :
    compactTok (GF := GF) γ c ⊢ compactTok γ c' := by
  unfold compactTok
  iintro ⟨%c₀, %h₀, H⟩
  iexists c₀
  iframe H
  ipureintro; omega

/-- **The compaction jobs' queue** at `c` (exclusive; 2026-10-13, unit 5c): the store's
scheduler's queue of tracked jobs (`schedule.schedQueue`), whose last name `p` saves the `Post`
`Q` of the last compaction job scheduled (or, before any, the scheduler's initial `True`), and a
resource `R` which, with `Q`, gives the index compactor's token at or below `c` (`compactTok`):
the next compaction job, tracked, gets `Q` from the scheduler (its `Prev`: the previous job has
run) and `R` from its caller (its `Pre`). Before any compaction, `Q = True` and `R` the token
itself (`NewStore`); after, `Q` the token, `R = True`. The request path's `run` threads the apply
thread's resources the same way. -/
def compactQueue (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(∃ (Ps : List GName) (p : GName) (Q R : IProp GF),
    schedule.schedQueue γ.sch (Ps ++ [p]) ∗ schedule.savedProp p Q ∗ R ∗ (Q ∗ R -∗ compactTok γ c))

/-- The queue is good at any higher revision. -/
theorem compactQueue_mono (γ : StoreNames) (c c' : Int) (h : c ≤ c') :
    compactQueue (GF := GF) γ c ⊢ compactQueue γ c' := by
  unfold compactQueue
  iintro ⟨%Ps, %p, %Q, %R, Hq, #Hp, HR, Hw⟩
  iexists Ps, p, Q, R
  iframe Hq Hp HR
  iintro HQR
  ihave Ht := Hw $$ HQR
  iapply compactTok_mono γ c c' h $$ Ht

/-- **The compaction right** at `c`: half the compaction revision's authority (the other halves
are a quarter under each of `s.mu` and `s.revMu`, `muInv`, `revMuInv`), and the compaction jobs'
queue (`compactQueue`: the scheduler's tracked queue, its last job's `Post` giving the index
compactor's token at or below `c`; 2026-10-13, unit 5c). `NewStore` returns it at `-1`;
`store.Compact` takes it (it updates the revision under both locks, which hold the rest of the
authority, then schedules the job, tracked, after `s.mu` is released: the right is what carries
the queue there) and returns it at the new revision. It also says the scheduler is never stopped
(`schedLive`: the compaction's barrier jobs are untracked; D19m (C), 2026-10-18: until then
`isStore` said it). `NewStore` returns the authority's half and the queue apart, the queue with
the stop token in the right to close the store (`storeCloser`); the caller that will not close
the store makes the right of them (`compactRight_of_closer`). -/
def compactRight (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(crevUB γ.idx (1 : Qp).half c ∗ compactQueue γ c ∗ schedule.schedLive γ.sch)

/-- The invariant's name of a frozen compaction revision. -/
abbrev crevFrozenN : Namespace := nroot.@"mvcc_crevFrozen"

/-- **No compaction, ever** (persistent): the compaction right at `-1`, given up into an
invariant (`compactRight_freeze`; its half of the revision's authority, the jobs' queue dropped),
so the revision stays `-1` (no one can gather the authority
to update it). The store's readers and writers as the txn, apply, request path and watchable
store use them (`storeReader`, and the transactions at their defaults: `isTxnRead`, …) carry it:
their statements are of a store that is not compacted (the frozen corollaries, `spec_frozen`, of
the store's general specs; 2026-10-13, unit 6a). -/
def crevFrozen (γ : StoreNames) : IProp GF := inv crevFrozenN (crevUB γ.idx (1 : Qp).half (-1))

instance crevFrozen_persistent (γ : StoreNames) : Persistent (crevFrozen (GF := GF) γ) := by
  unfold crevFrozen; infer_instance

/-- **A compaction revision safe for readers** (persistent; 2026-10-13, unit 6a): a certified
log with revision `c` that does not delete a key and put it again (`NoDelPutAt`, `Compact.lean`:
else compaction at `c` deletes the key's live value, `issues/etcd-compaction-delete-then-put.md`).
`NoDelPutAt` depends on revision `c` alone (`NoDelPutAt_prefix`), so it holds of every certified log
with that revision (`crevSafe_cert`). The one who compacts asserts it (`store.Compact`'s premise);
`s.mu`'s resource keeps it for the current compaction revision (`muInvAt`), the keys compaction
may delete for theirs (`delKey`). Trivial at `c < 0` (`crevSafe_neg`). -/
def crevSafe (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(∃ log : Log, idxCert γ.idx log ∗ ⌜c < log.length ∧ NoDelPutAt log c⌝)

instance crevSafe_persistent (γ : StoreNames) (c : Int) : Persistent (crevSafe (GF := GF) γ c) := by
  unfold crevSafe; infer_instance

/-- With no compaction, any certified log with a revision. -/
theorem crevSafe_neg (γ : StoreNames) (c : Int) (log : Log) (hc : c < 0) (hl : c < log.length) :
    idxCert (GF := GF) γ.idx log ⊢ crevSafe γ c := by
  iintro #H
  iunfold crevSafe
  iexists log
  iframe H
  ipureintro; exact ⟨hl, NoDelPutAt_neg hc⟩

/-- **Every certified log with revision `c` is safe at `c`** if one is. -/
theorem crevSafe_cert (γ : StoreNames) (c : Int) (log : Log) (hl : c < log.length) :
    crevSafe (GF := GF) γ c ∗ idxCert γ.idx log ⊢ ⌜NoDelPutAt log c⌝ := by
  iintro ⟨Hs, #Hc⟩
  iunfold crevSafe at Hs
  icases Hs with ⟨%log', #Hc', %Hl'⟩
  ihave %Hp := idxCert_prefix γ.idx log log' $$ [$Hc $Hc']
  ipureintro
  rcases Hp with h | h
  · exact (NoDelPutAt_prefix h hl).1 Hl'.2
  · exact (NoDelPutAt_prefix h Hl'.1).2 Hl'.2

/-- **A key compaction may delete** (persistent, the store's choice of the backend contract's
`Del`): of a certified log, a revision's bytes compaction at a lower bound `c` of the
compaction revision may delete (`KeyDel`, `Compact.lean`), revision `c` of the log not deleting
then putting a key (`NoDelPutAt`: the compactor's assertion, `compactJobPre`; 2026-10-13, unit 6a):
so a read at or above the compaction revision never names one (`rangeAnswers_not_del`). -/
def delKey (γ : StoreNames) (k : GoString) : IProp GF :=
  iprop(∃ (c : Int) (log : Log), crevLb γ.idx c ∗ idxCert γ.idx log ∗
    ⌜-1 ≤ c ∧ KeyDel log c k ∧ NoDelPutAt log c⌝)

/-- `delKey` is timeless (ghost lower bounds and pure facts; the backend-compaction stage, review
round 2, Target 4): so the store's deletable keys can be instantiated as `◇ delKey`, which the
backend's saved-predicate registration gives without a step (`▷ delKey ⊢ ◇ delKey`). -/
instance delKey_timeless (γ : StoreNames) (k : GoString) : Timeless (delKey (GF := GF) γ k) := by
  unfold delKey idxCert crevLb; infer_instance

instance delKey_persistent (γ : StoreNames) (k : GoString) : Persistent (delKey (GF := GF) γ k) := by
  unfold delKey; infer_instance

/-- Two parts of the compaction revision's authority agree. -/
theorem crevUB_agree (γ : IdxNames) (q1 q2 : Qp) (c1 c2 : Int) (h1 : -1 ≤ c1) (h2 : -1 ≤ c2) :
    ⊢ crevUB (GF := GF) γ q1 c1 -∗ crevUB γ q2 c2 -∗ ⌜c1 = c2⌝ := by
  unfold crevUB
  iintro H1 H2
  ihave %h := monoNatAuthOwn_agree γ.crev q1 q2 _ _ $$ H1 H2
  ipureintro
  have := h.2
  unfold crevN at this
  omega

theorem crevUB_split (γ : IdxNames) (q1 q2 : Qp) (c : Int) :
    crevUB (GF := GF) γ (q1 + q2) c ⊣⊢ crevUB γ q1 c ∗ crevUB γ q2 c := by
  unfold crevUB
  exact (monoNatAuthOwn_fractional (GF := GF) γ.crev (crevN c)).fractional q1 q2

/-- A part of the authority bounds every lower bound (the part kept). -/
theorem crevUB_lb_keep (γ : IdxNames) (q : Qp) (c c' : Int) (hc : -1 ≤ c) :
    crevUB (GF := GF) γ q c ∗ crevLb γ c' ⊢ crevUB γ q c ∗ ⌜c' ≤ c⌝ := by
  have key : crevUB (GF := GF) γ q c ∗ crevLb γ c' ⊢ ⌜c' ≤ c⌝ := by
    iintro ⟨Ha, #Hl⟩
    unfold crevUB crevLb
    ihave %h := monoNatLbOwn_valid γ.crev q _ _ $$ Ha Hl
    ipureintro
    by_cases hc' : -1 ≤ c'
    · exact crevN_le hc' hc h.2
    · omega
  exact (and_intro sep_elim_left key).trans persistent_and_sep_mp

/-- A part of the authority gives a lower bound (the part kept). -/
theorem crevUB_get_lb (γ : IdxNames) (q : Qp) (c : Int) :
    crevUB (GF := GF) γ q c ⊢ crevUB γ q c ∗ crevLb γ c := by
  have key : crevUB (GF := GF) γ q c ⊢ crevLb γ c := by
    unfold crevUB crevLb
    iintro Ha
    iapply monoNatLbOwn_get γ.crev q _ $$ Ha
  exact (and_intro .rfl key).trans persistent_and_sep_mp

/-- With a part of the compaction revision's authority at `-1`, no key is deletable. -/
theorem crevUB_noDel (γ : StoreNames) (q : Qp) (k : GoString) :
    ⊢ crevUB (GF := GF) γ.idx q (-1) -∗ delKey γ k -∗ False := by
  iintro Hc Hd
  iunfold delKey at Hd
  icases Hd with ⟨%c, %log, #Hlb, -, %Hk⟩
  ihave %Hle := crevUB_lb γ.idx q (-1) c (by decide) Hk.1 $$ Hc Hlb
  exact (KeyDel_neg (show c < 0 by omega) Hk.2.1).elim

/-- **A snapshot of a store not compacted is the bucket**: with a part of the compaction
revision's authority at `-1` (kept), a thinned snapshot misses no key. -/
theorem snapThin_crev (γ : StoreNames) (q : Qp) (m m' : Bucket) :
    crevUB (GF := GF) γ.idx q (-1) ∗ snapThin m m' (delKey γ) ⊢
      crevUB γ.idx q (-1) ∗ ⌜m' = m⌝ := by
  iintro ⟨Hc, Ht⟩
  iunfold snapThin at Ht
  icases Ht with ⟨%Hsub, #Hdel⟩
  by_cases h : ∀ k, m'.lookup k = m.lookup k
  · iframe Hc; ipureintro; exact GMap.ext h
  · have : ∃ k, m'.lookup k ≠ m.lookup k := Classical.byContradiction fun hn =>
      h fun k => Classical.byContradiction fun hk => hn ⟨k, hk⟩
    obtain ⟨k, hk⟩ := this
    cases hm : m.lookup k with
    | none =>
      cases hm' : m'.lookup k with
      | none => exact absurd (hm'.trans hm.symm) hk
      | some v => rw [Hsub k v hm'] at hm; cases hm
    | some v =>
      cases hm' : m'.lookup k with
      | none =>
        ihave Hd := Hdel $$ %k %v
        ispecialize Hd $$ []
        · ipureintro; exact ⟨hm, hm'⟩
        ihave %F := crevUB_noDel γ q k $$ Hc Hd
        exact F.elim
      | some v' => have := Hsub k v' hm'; rw [hm] at this; rw [hm', hm, this] at hk; exact absurd rfl hk

/-- **Freezing** from the compaction right's half of the revision's authority at `-1` (what
`NewStore` returns besides the right to close the store): no compaction, ever. -/
theorem crevFrozen_alloc (γ : StoreNames) (E : CoPset) :
    ⊢ crevUB (GF := GF) γ.idx (1 : Qp).half (-1) ={E}=∗ crevFrozen γ := by
  iintro H
  iunfold crevFrozen
  iapply inv_alloc
  inext
  iexact H

/-- A frozen compaction revision is `-1`. -/
theorem crevFrozen_agree (γ : StoreNames) (q : Qp) (c : Int) (hc : -1 ≤ c) :
    ⊢ crevFrozen (GF := GF) γ -∗ crevUB γ.idx q c ={⊤}=∗ crevUB γ.idx q c ∗ ⌜c = -1⌝ := by
  iintro #Hf Hc
  iunfold crevFrozen at Hf
  imod inv_acc (E := ⊤) (N := crevFrozenN) (P := crevUB (GF := GF) γ.idx (1 : Qp).half (-1))
    (by exact CoPset.subseteq_top) $$ Hf with ⟨>Hr, Hclose⟩
  ihave %Heq := crevUB_agree γ.idx q (1 : Qp).half c (-1) hc (by decide) $$ Hc Hr
  imod Hclose $$ [Hr] with -
  · inext; iexact Hr
  imodintro
  iframe Hc
  ipureintro; exact Heq

/-- **A snapshot of a frozen store is the bucket.** -/
theorem snapThin_frozen (γ : StoreNames) (m m' : Bucket) :
    ⊢ crevFrozen (GF := GF) γ -∗ snapThin m m' (delKey γ) ={⊤}=∗ ⌜m' = m⌝ := by
  iintro #Hf #Ht
  iunfold crevFrozen at Hf
  imod inv_acc (E := ⊤) (N := crevFrozenN) (P := crevUB (GF := GF) γ.idx (1 : Qp).half (-1))
    (by exact CoPset.subseteq_top) $$ Hf with ⟨>Hr, Hclose⟩
  icases snapThin_crev γ (1 : Qp).half m m' $$ [$Hr $Ht] with ⟨Hr, %Heq⟩
  imod Hclose $$ [Hr] with -
  · inext; iexact Hr
  imodintro
  ipureintro; exact Heq

/-- The lower bound `-1` of the compaction revision (none): a ghost update from nothing. -/
theorem crevLb_neg (γ : IdxNames) : ⊢ |==> crevLb (GF := GF) γ (-1) := by
  unfold crevLb
  rw [crevN_neg]
  exact monoNatLbOwn_0 γ.crev

/-- **A frozen compaction revision bounds every lower bound**: `-1`. -/
theorem crevFrozen_lb (γ : StoreNames) (c : Int) (hc : -1 ≤ c) :
    ⊢ crevFrozen (GF := GF) γ -∗ crevLb γ.idx c ={⊤}=∗ ⌜c = -1⌝ := by
  iintro #Hf #Hl
  iunfold crevFrozen at Hf
  imod inv_acc (E := ⊤) (N := crevFrozenN) (P := crevUB (GF := GF) γ.idx (1 : Qp).half (-1))
    (by exact CoPset.subseteq_top) $$ Hf with ⟨>Hr, Hclose⟩
  ihave %Hle := crevUB_lb γ.idx (1 : Qp).half (-1) c (by decide) hc $$ Hr Hl
  imod Hclose $$ [Hr] with -
  · inext; iexact Hr
  imodintro
  ipureintro; omega

/-- **The meta keys' record** at fraction `q`: the values the store last wrote at
`scheduledCompactRev` and `finishedCompactRev` (`none`: never), its own view of the `Meta`
bucket's compaction keys (not `MetaCI`, the consistent index's). The batch lock holds it. -/
def metaCompact (γ : StoreNames) (q : Qp) (sched fin : Option w64) : IProp GF :=
  ghostVar γ.cmeta q (sched, fin)

/-- A finished compaction's revision as an integer (`-1`: none). -/
def finRev : Option w64 → Int
  | some x => sint.Z x
  | none => -1

/-- **A compaction at `rev` finished** (persistent): the job set `finishedCompactRev` to `rev`
or a later compaction's (a lower bound of the finished revision's counter, whose authority the
batch lock holds with the meta keys' record). -/
def compactedAt (γ : StoreNames) (rev : Int) : IProp GF := monoNatLbOwn γ.fin (crevN rev)

instance compactedAt_persistent (γ : StoreNames) (rev : Int) :
    Persistent (compactedAt (GF := GF) γ rev) := by
  unfold compactedAt; infer_instance

/-- The compaction's part of the batch lock's resource: the meta keys' record and the finished
compactions' counter, at or above the record's finished revision (the highest revision a job
finished at: the jobs run in the order of their revisions, but the batch lock's resource does not
know it, so a job finishing writes its revision and raises the counter to it, if below;
2026-10-13, unit 5c, contract correction: the counter was the record's revision exactly). -/
def compactRes (γ : StoreNames) : IProp GF :=
  iprop(∃ (sched fin : Option w64) (n : Nat), metaCompact γ 1 sched fin ∗
    monoNatAuthOwn γ.fin 1 n ∗ ⌜crevN (finRev fin) ≤ n⌝)

/-! ## The locks -/

/-! ## The locks -/


/-- Two halves of a ghost variable agree and make the whole. -/
theorem ghostVar_join_halves {A : Type} [Pos.Countable A] (γ : GName) (a b : A) :
    ghostVar (GF := GF) γ (1 : Qp).half a ∗ ghostVar γ (1 : Qp).half b ⊢
      ghostVar γ 1 a ∗ ⌜a = b⌝ := by
  iintro ⟨H1, H2⟩
  ihave %Hab := ghostVar_agree γ a _ b _ $$ H1 H2
  subst Hab
  have h := (ghostVar_fractional (GF := GF) γ a).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  isplitl
  · iapply h.2; iframe H1 H2
  ipureintro; rfl

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

/-- A holder of `s.mu` shared has two deposits (D22 receiver epochs, S4: one for the readers'
pool, one for the writer's invariant or its read transaction). -/
theorem wDep_halves (γ : StoreNames) :
    ghostVar (GF := GF) γ.wr sync.rfrac () ⊣⊢ wDep γ ∗ wDep γ := by
  unfold wDep; exact ghostVar_split_half γ.wr sync.rfrac ()

/-- The batch lock's resource for the store (`W` of `isKeyBackend`; physical, per backend: D22
receiver epochs, S2, 2026-10-22, until then also the writer's state, now `writerL`): the batch
lock's key, half the ghost of the log `L` the bucket's view is of (the other half is the
writer's state's, so the writer's log is the view's), half the bucket's view at `L` (the other
half under `s.revMu`: the write transaction's reads of the bucket, through the batch transaction),
the certificate of `L`, and the compaction's part (`compactRes`: the meta keys' record, the
finished compactions' counter). -/
def writerRes (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ L : Log,
    "Hwk" ∷ writerKey γ ∗
    "Hwv" ∷ ghostVar γ.wv (1 : Qp).half L ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap L) ∗
    "#Hcert" ∷ idxCert γ.idx L ∗
    "%Hne" ∷ ⌜L ≠ []⌝ ∗
    "Hcres" ∷ compactRes γ)

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
    "Hlrd" ∷ lease.lessorRdOf γ.leases)

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

instance storeRegd_persistent (s : Loc) (γ : StoreNames) :
    Persistent (storeRegd (GF := GF) s γ) := by
  unfold storeRegd; cases γ.kb <;> simp only <;> infer_instance

/-- The right to register a store in the instance `kb`. -/
def kbRegRight (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => lateReg d.gx

/-- The registered store's lock resource is its writer's resource. -/
theorem storeW_get (s : Loc) (γ : StoreNames) :
    storeRegd (GF := GF) s γ ∗ storeW s γ ⊢ writerRes s γ := by
  unfold storeRegd storeW
  cases γ.kb with
  | none => simp only; iintro ⟨-, H⟩; iexact H
  | some d =>
    simp only
    unfold lateW
    iintro ⟨#Hr, (H | ⟨%s', %γ', #Hr', H⟩)⟩
    · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hr H
      cases Hc
    · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hr Hr'
      cases Hc
      iexact H

/-- The registered store's writer's resource is its lock resource. -/
theorem storeW_put (s : Loc) (γ : StoreNames) :
    storeRegd (GF := GF) s γ ∗ writerRes s γ ⊢ storeW s γ := by
  unfold storeRegd storeW
  cases γ.kb with
  | none => simp only; iintro ⟨-, H⟩; iexact H
  | some d =>
    simp only
    unfold lateW
    iintro ⟨#Hr, H⟩
    iright
    iexists s, γ
    iframe Hr H

/-- **The registration** (`NewStore`'s first `Unlock`): the lock's initial resource and the
right to register, with the store's writer's resource, make the store's lock resource, the store
registered. -/
theorem storeW_register (s : Loc) (γ : StoreNames) :
    kbWi (GF := GF) γ.kb ∗ kbRegRight γ.kb ∗ writerRes s γ ==∗ storeW s γ ∗ storeRegd s γ := by
  unfold kbWi kbRegRight storeW storeRegd
  cases hk : γ.kb with
  | none => simp only; iintro ⟨-, -, H⟩; imodintro; iframe H
  | some d =>
    simp only
    unfold lateW lateReg
    iintro ⟨(H1 | ⟨%s', %γ', #Hr', -⟩), H2, HW⟩
    · imod dghostVar_update_halves (some (s, γ)) d.gx _ _ $$ H1 H2 with ⟨H1, -⟩
      imod dghostVar_persist d.gx _ _ $$ H1 with #H
      imodintro
      isplitl [HW]
      · iright
        iexists s, γ
        iframe H HW
      iexact H
    · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hr' H2
      cases Hc

/-- The writer's invariant's name. -/
abbrev writerN : Namespace := nroot.@"mvcc_writer"

/-- **The writer's registration in its backend** (D22 receiver epochs, S6, 2026-10-22): the store
`(s, γ)` registered in its backend's late-bound lock slot (`storeRegd`), or not yet, with the right
to register it and the batch lock's resource to deposit (`kbRegRight`, `writerRes`): after
`store.Restore`, whose new backend's batch lock holds its unregistered `lateW` (`Restore` does not
take the batch lock), until the next writer's `LockInsideApply` registers it
(`writerInv_checkout`). `NewStore` registers at its first `Unlock`. -/
def writerReg (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(storeRegd s γ ∨ kbRegRight γ.kb ∗ writerRes s γ)

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
S6 in `physOk`: a restored backend is registered only at its first writer's lock). -/
def writerInvBody (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop((∃ (p : PhysNames) (o : StoreObjs),
    curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
    (writerL s (γ.withPhys p) ∗ writerReg s (γ.withPhys p) ∨
      writerKey (γ.withPhys p) ∗ wDep γ ∗ storeRegd s (γ.withPhys p))) ∨
    ghostVar γ.wr 1 () ∗ ∃ h : List HistItem, monoListAuthOwn γ.idx.hist (1 : Qp).half h)

/-- The writer's invariant (`writerInvBody`). -/
def writerInv (s : Loc) (γ : StoreNames) : IProp GF :=
  inv writerN (writerInvBody s γ)

instance writerInv_persistent (s : Loc) (γ : StoreNames) : Persistent (writerInv (GF := GF) s γ) := by
  unfold writerInv; infer_instance

/-- **A pending registration, made at the writer's lock** (D22 receiver epochs, S6): the lock's
resource (unregistered, for the real backend: the right to register's other half), the right to
register and the writer's resource register the store; mvcc's assumed backend's lock holds the
writer's resource itself. -/
theorem storeW_pending (s : Loc) (γ : StoreNames) :
    storeW (GF := GF) s γ ∗ kbRegRight γ.kb ∗ writerRes s γ ==∗ writerRes s γ ∗ storeRegd s γ := by
  unfold storeW kbRegRight storeRegd
  cases hk : γ.kb with
  | none => simp only; iintro ⟨H, -, -⟩; imodintro; iframe H
  | some d =>
    simp only
    unfold lateW lateReg
    iintro ⟨(H1 | ⟨%s', %γ', #Hr', -⟩), H2, HW⟩
    · imod dghostVar_update_halves (some (s, γ)) d.gx _ _ $$ H1 H2 with ⟨H1, -⟩
      imod dghostVar_persist d.gx _ _ $$ H1 with #H
      imodintro
      iframe H HW
    · ihave %Hc := dghostVar_agree d.gx _ _ _ _ $$ Hr' H2
      cases Hc

/-- **The store's backend contract over mvcc's assumed backend** (`storeCmp γ`, `γ.kb = none`;
2026-10-13, unit 5c): no tokens, no condition on the puts, the lock resource the writer's
(`writerRes`), the compaction's calls (`Cmp` true). -/
theorem isKeyBackendG_cmp (b : GoInterface) (s : Loc) (γ : StoreNames) (Dep P : IProp GF) (HF : val → IProp GF)
    (h : storeCmp γ) :
    isKeyBackendG (GF := GF) b (bucketView γ) (storeRT γ) (storeWT γ) (kbNoCmp γ.kb γ.bucket)
      (storePutOk γ) (delKey γ)
      (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) P HF (storeReq γ) (storeRb γ) (storeBt γ)
      (MW := kbMW γ.kb) ⊢
    isKeyBackendG b (bucketView γ) iprop(True) iprop(True) (kbNoCmp γ.kb γ.bucket) noPutCond
      (delKey γ) (writerRes s γ) iprop(True) Dep True P HF (MW := kbMW none) := by
  unfold storeCmp kbCmp at h
  unfold storeW kbWi storeRT storeWT storePutOk storeCmp kbCmp kbRT kbWT kbPutOk storeReq kbReq
    storeRb kbRb storeBt kbBt
  simp only [h]
  exact .rfl

/-- **A caller's lent fraction of the committed log's authority** (unit W-K): `some (q, L)`, the
fraction `q` at `L` (a reader holding it knows the committed log is `L`: `store.Read` finds it so);
`none`, nothing. -/
def logLent (γ : IdxNames) : Option (Qp × Log) → IProp GF
  | some (q, L) => idxLogAuth γ q L
  | none => iprop(True)

/-- A lent fraction agrees with another's. -/
theorem logLent_agree (γ : IdxNames) (q0 : Qp) (log : Log) (oa : Option (Qp × Log)) :
    idxLogAuth (GF := GF) γ q0 log ∗ logLent γ oa ⊢
      idxLogAuth γ q0 log ∗ logLent γ oa ∗ ⌜∀ q L, oa = some (q, L) → log = L⌝ := by
  cases oa with
  | none =>
    iintro ⟨H, -⟩
    iframe H
    unfold logLent
    isplitr
    · itrivial
    ipureintro; intro q L h; cases h
  | some p =>
    obtain ⟨q, L⟩ := p
    iintro ⟨H, Hl⟩
    unfold logLent at *
    ihave %Hag := monoListAuthOwn_agree γ.log q0 q log L $$ H Hl
    iframe H Hl
    ipureintro; intro q' L' h; cases h; exact Hag.2

/-- **The committed log `log` is certified OK by the caller** (persistent; 2026-10-14, unit T1):
`NewStore`'s logs (at most two revisions), or an element of the caller's map `γ.cok`. -/
def certOk (γ : StoreNames) (log : Log) : IProp GF :=
  iprop(⌜log.length ≤ 2⌝ ∨ (W64 (log.length : Int)) ↪[γ.cok]□ log ∨ (W64 0) ↪[γ.cok]□ ([] : Log))

/-- **Every log is certified** (persistent): the map's free mode, the element `0 ↦ []` (a caller
that does not use the certificates mints it; no committed log has length `0`, so a caller that does,
the etcd server, never holds it). -/
def certFree (γ : StoreNames) : IProp GF := (W64 0) ↪[γ.cok]□ ([] : Log)

instance certFree_persistent (γ : StoreNames) : Persistent (certFree (GF := GF) γ) := by
  unfold certFree; infer_instance

open Iris.ProofMode in
theorem certFree_certOk (γ : StoreNames) (log : Log) : certFree (GF := GF) γ ⊢ certOk γ log := by
  unfold certFree certOk
  iintro #H
  iright; iright; iexact H

instance certOk_persistent (γ : StoreNames) (log : Log) : Persistent (certOk (GF := GF) γ log) := by
  unfold certOk; infer_instance

instance certOk_timeless (γ : StoreNames) (log : Log) : Timeless (certOk (GF := GF) γ log) := by
  unfold certOk; infer_instance

/-- What a commit of `pend` after `ilog` needs: nothing for no change, else the certificate of the
log after (2026-10-14, unit T1). -/
def certOkNext (γ : StoreNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(⌜pend = []⌝ ∨ certOk γ (ilog ++ [pend]))

instance certOkNext_persistent (γ : StoreNames) (ilog : Log) (pend : List Change) :
    Persistent (certOkNext (GF := GF) γ ilog pend) := by
  unfold certOkNext; infer_instance

/-- **The outer quarter of the committed log's authority** (the watch slice's unit W-K):
`s.revMu` holds a quarter (`revMuInv`), the index writer half (`idxWriter`), and the store's
owner the last quarter: the watchable store's `s.mu` (`watchStoreBody`, at the notified log, so
that a reader under `s.mu` finds every certified log a prefix of the notified one), or the sole
writer (`soleWriter`) of a store used without watchers. A commit (`storeTxnWrite.End` with
changes) takes it and gives it back at the committed log. -/
abbrev logQ (γ : StoreNames) (log : Log) : IProp GF := idxLogAuth γ.idx (1 : Qp).half.half log

/-- `s.revMu`'s fraction of the committed log's authority, at its lock's fraction `q`: a quarter
for a watchable store's (the outer quarter is `s.mu`'s), a half otherwise. -/
def revQ (γ : StoreNames) (q : Qp) : Qp := if γ.watchQ then q.half.half else q.half

theorem revQ_add (γ : StoreNames) (q1 q2 : Qp) : revQ γ (q1 + q2) = revQ γ q1 + revQ γ q2 := by
  unfold revQ; split <;> simp [Qp_half_add]

/-- What a commit of `pend` after `ilog` takes of the outer quarter: nothing for no change, nor
for a store without watchers. -/
def logQPre (γ : StoreNames) (ilog : Log) (pend : List Change) : IProp GF :=
  if pend = [] ∨ γ.watchQ = false then iprop(True) else logQ γ ilog

/-- What a commit of `pend` after `ilog` gives back: the outer quarter at the committed log. -/
def logQPost (γ : StoreNames) (ilog : Log) (pend : List Change) : IProp GF :=
  if pend = [] ∨ γ.watchQ = false then iprop(True) else logQ γ (ilog ++ [pend])

@[simp] theorem logQPre_nil (γ : StoreNames) (ilog : Log) :
    logQPre (GF := GF) γ ilog [] = iprop(True) := by unfold logQPre; simp

@[simp] theorem logQPost_nil (γ : StoreNames) (ilog : Log) :
    logQPost (GF := GF) γ ilog [] = iprop(True) := by unfold logQPost; simp

theorem logQPre_plain (γ : StoreNames) (ilog : Log) (pend : List Change) (h : γ.watchQ = false) :
    logQPre (GF := GF) γ ilog pend = iprop(True) := by unfold logQPre; simp [h]

theorem logQPost_plain (γ : StoreNames) (ilog : Log) (pend : List Change) (h : γ.watchQ = false) :
    logQPost (GF := GF) γ ilog pend = iprop(True) := by unfold logQPost; simp [h]

theorem logQPre_ne (γ : StoreNames) (ilog : Log) (pend : List Change) (h : pend ≠ [])
    (hw : γ.watchQ = true) : logQPre (GF := GF) γ ilog pend = logQ γ ilog := by
  unfold logQPre; simp [h, hw]

theorem logQPost_ne (γ : StoreNames) (ilog : Log) (pend : List Change) (h : pend ≠ [])
    (hw : γ.watchQ = true) : logQPost (GF := GF) γ ilog pend = logQ γ (ilog ++ [pend]) := by
  unfold logQPost; simp [h, hw]

open Iris.ProofMode in
theorem certFree_certOkNext (γ : StoreNames) (ilog : Log) (pend : List Change) :
    certFree (GF := GF) γ ⊢ certOkNext γ ilog pend := by
  iintro #H
  unfold certOkNext
  iright
  iapply certFree_certOk $$ H

/-- `s.revMu`'s resource at fraction `q`: the committed log `log`'s last revision in
`currentRev` (half of it: the writer's state holds the other half, `writerL`), half the
committed-log ghost variable, the index's certificate of `log` and the bucket's authority
(`bucketMap log`, half of it: the batch lock holds the other half), half the revision
budget's authority with its bound for `log`, and half the committed log's authority (the index
writer holds the other half; a quarter for a watchable store's, `revQ`); and the compaction revision `c` (at most the committed log's
last revision): half `compactMainRev`'s points-to and a quarter of its authority (`s.mu` holds
as much: `store.Compact`, holding both locks, updates them; the watchable store's
`syncWatchers` reads it under `s.revMu`, a transaction's `rangeKeys` under `s.mu`). The bucket's
view and the index's count are of the physical names `γp` (D22 receiver epochs, S5b: the current
ones, `revMuInv`), the rest of the store's names `γ`. -/
def revMuBody (s : Loc) (γ γp : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (log : Log) (ntok : Nat) (c : Int),
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "#Hnev" ∷ idxNevLb γp.idx log ∗
    "#Hok" ∷ certOk γ log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketView γp q.half (bucketMap log) ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own q.half) ntok ∗
    "%Hbudget" ∷ ⌜log.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlog" ∷ idxLogAuth γ.idx (revQ γ q) log ∗
    "Hcmp" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 c : w64) : IProp GF) ∗
    "Hcrev" ∷ crevUB γ.idx q.half.half c ∗
    "%Hc" ∷ ⌜-1 ≤ c ∧ c < log.length⌝)

/-- `s.revMu`'s resource is fractional (for `sync.init_RWMutex`): the halves of `currentRev`,
of the ghost log and of the bucket's view split, and two parts agree on the log. -/
instance revMuBody_fractional (s : Loc) (γ γp : StoreNames) : Fractional (revMuBody (GF := GF) s γ γp) where
  fractional q1 q2 := by
    have hcur : ∀ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"currentRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"currentRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hclog := fun (log : Log) =>
      (ghostVar_fractional (GF := GF) γ.clog log).fractional q1.half q2.half
    have hbv := fun (m : Bucket) =>
      (bucketView_fractional (GF := GF) γp m).fractional q1.half q2.half
    have htk : ∀ n : Nat, ownTokAuthDfrac (GF := GF) γ.revs (DFrac.own (q1.half + q2.half)) n ⊣⊢
        ownTokAuthDfrac γ.revs (DFrac.own q1.half) n ∗ ownTokAuthDfrac γ.revs (DFrac.own q2.half) n :=
      fun n => ownTokAuthDfrac_split (GF := GF) γ.revs (DFrac.own q1.half) (DFrac.own q2.half) n
    have hlg := fun (log : Log) =>
      (monoListAuthOwn_fractional (GF := GF) γ.idx.log log).fractional (revQ γ q1) (revQ γ q2)
    have hcmp : ∀ v : w64, (s.[store, go!"compactMainRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"compactMainRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"compactMainRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hcrev := fun (c : Int) => crevUB_split (GF := GF) γ.idx q1.half.half q2.half.half c
    unfold revMuBody
    rw [revQ_add, Qp_half_add, Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro H
      icases H with ⟨%log, %ntok, %c, H⟩
      iNamed H
      icases (hcur _).1 $$ Hrev with ⟨Hr1, Hr2⟩
      icases (hclog log).1 $$ Hclog with ⟨Hc1, Hc2⟩
      icases (hbv _).1 $$ Hbucket with ⟨Hb1, Hb2⟩
      icases (htk ntok).1 $$ Htoks with ⟨Ht1, Ht2⟩
      icases (hlg log).1 $$ Hlog with ⟨Hl1, Hl2⟩
      icases (hcmp _).1 $$ Hcmp with ⟨Hm1, Hm2⟩
      icases (hcrev c).1 $$ Hcrev with ⟨Hv1, Hv2⟩
      isplitl [Hr1 Hc1 Hb1 Ht1 Hl1 Hm1 Hv1]
      · iexists log, ntok, c; simp only [named]; iframe Hr1 Hc1 Hb1 Ht1 Hl1 Hm1 Hv1; iframe #
        ipureintro
        exact ⟨Hne, Hbudget, Hc⟩
      · iexists log, ntok, c; simp only [named]; iframe Hr2 Hc2 Hb2 Ht2 Hl2 Hm2 Hv2; iframe #
        ipureintro
        exact ⟨Hne, Hbudget, Hc⟩
    · iintro ⟨H1, H2⟩
      icases H1 with ⟨%log, %ntok, %c, H1⟩
      icases H2 with ⟨%log2, %ntok2, %c2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      ihave %Hlog := ghostVar_agree γ.clog _ _ _ _ $$ Hclog1 Hclog2
      subst Hlog
      icombine Htoks1 Htoks2 gives %Hn
      obtain ⟨-, Hn⟩ := Hn
      subst Hn
      ihave %Hcc := crevUB_agree γ.idx _ _ c c2 Hc1.1 Hc2.1 $$ Hcrev1 Hcrev2
      subst Hcc
      iexists log, ntok, c
      simp only [named]
      isplitl [Hrev1 Hrev2]
      · iapply (hcur _).2; iframe Hrev1 Hrev2
      isplitl [Hclog1 Hclog2]
      · iapply (hclog log).2; iframe Hclog1 Hclog2
      isplitr
      · iexact Hcert1
      isplitr
      · iexact Hnev1
      isplitr
      · iexact Hok1
      isplitr
      · ipureintro; exact Hne1
      isplitl [Hbucket1 Hbucket2]
      · iapply (hbv _).2; iframe Hbucket1 Hbucket2
      isplitl [Htoks1 Htoks2]
      · iapply (htk ntok).2; iframe Htoks1 Htoks2
      isplitl []
      · ipureintro; exact Hbudget1
      isplitl [Hlog1 Hlog2]
      · iapply (hlg log).2; iframe Hlog1 Hlog2
      isplitl [Hcmp1 Hcmp2]
      · iapply (hcmp _).2; iframe Hcmp1 Hcmp2
      isplitl [Hcrev1 Hcrev2]
      · iapply (hcrev c).2; iframe Hcrev1 Hcrev2
      ipureintro; exact Hc1

/-- **`s.revMu`'s resource while `store.Restore` restores** (D22 receiver epochs, S3, 2026-10-22):
`Restore` sets `currentRev = 1` and `compactMainRev = -1` under `s.revMu` and releases it before the
restored revision is known (`kvstore.go:302-307`), so the lock holds only its parts of the two
counters, at any values; `Restore` holds the rest. No verified reader sees it: every reader of
`s.revMu` holds `s.mu` or a watchable store's `s.mu`, and with it a part of the fields' share with
the restoring flag down (`fieldShare`, `revMuInv_open`). -/
def revMuRest (s : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (v c : w64), (s.[store, go!"currentRev"] ↦{DFrac.own q.half} v : IProp GF) ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} c : IProp GF))

instance revMuRest_fractional (s : Loc) : Fractional (revMuRest (GF := GF) s) where
  fractional q1 q2 := by
    have hcur : ∀ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"currentRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"currentRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hcmp : ∀ v : w64, (s.[store, go!"compactMainRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"compactMainRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"compactMainRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    unfold revMuRest
    rw [Qp_half_add]
    constructor
    · iintro ⟨%v, %c, Hv, Hc⟩
      icases (hcur v).1 $$ Hv with ⟨Hv1, Hv2⟩
      icases (hcmp c).1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [Hv1 Hc1]
      · iexists v, c; iframe Hv1 Hc1
      · iexists v, c; iframe Hv2 Hc2
    · iintro ⟨⟨%v1, %c1, Hv1, Hc1⟩, ⟨%v2, %c2, Hv2, Hc2⟩⟩
      icombine Hv1 Hv2 gives %Hv
      icombine Hc1 Hc2 gives %Hc
      obtain ⟨-, rfl⟩ := Hv
      obtain ⟨-, rfl⟩ := Hc
      iexists v1, c1
      isplitl [Hv1 Hv2]
      · iapply (hcur v1).2; iframe Hv1 Hv2
      iapply (hcmp c1).2; iframe Hc1 Hc2

/-- **`s.revMu`'s resource, at the current physical names** at fraction `q` (D22 receiver epochs,
S5b): an eighth of the fraction of the store's current objects and names, at `p`, and the resource
`revMuBody` with the bucket's view and the index's count of `p`'s names. -/
def revMuCur (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (p : PhysNames) (o : StoreObjs), curAt (γ.withPhys p) (DFrac.own q.half.half.half) o ∗
    revMuBody s γ (γ.withPhys p) q)

theorem curAt_withPhys_agree (γ : StoreNames) (p1 p2 : PhysNames) (dq1 dq2 : DFrac)
    (o1 o2 : StoreObjs) :
    curAt (GF := GF) (γ.withPhys p1) dq1 o1 ∗ curAt (γ.withPhys p2) dq2 o2 ⊢ ⌜o1 = o2 ∧ p1 = p2⌝ := by
  iintro H
  ihave %Hv := curAt_agree (γ.withPhys p1) (γ.withPhys p2) rfl dq1 dq2 o1 o2 $$ H
  ipureintro
  exact ⟨Hv.1, by have h2 := Hv.2; simp only [StoreNames.withPhys_phys] at h2; exact h2⟩

instance revMuCur_fractional (s : Loc) (γ : StoreNames) : Fractional (revMuCur (GF := GF) s γ) where
  fractional q1 q2 := by
    unfold revMuCur
    rw [Qp_half_add, Qp_half_add, Qp_half_add]
    constructor
    · iintro ⟨%p, %o, Hc, H⟩
      icases (curAt_fractional (GF := GF) (γ.withPhys p) o).fractional _ _ |>.1 $$ Hc with ⟨Hc1, Hc2⟩
      icases (revMuBody_fractional (GF := GF) s γ (γ.withPhys p)).fractional q1 q2 |>.1 $$ H
        with ⟨H1, H2⟩
      isplitl [Hc1 H1]
      · iexists p, o; iframe Hc1 H1
      · iexists p, o; iframe Hc2 H2
    · iintro ⟨⟨%p1, %o1, Hc1, H1⟩, ⟨%p2, %o2, Hc2, H2⟩⟩
      ihave %Hv := curAt_withPhys_agree γ p1 p2 _ _ o1 o2 $$ [Hc1 Hc2]
      · iframe Hc1 Hc2
      obtain ⟨rfl, rfl⟩ := Hv
      iexists p1, o1
      isplitl [Hc1 Hc2]
      · iapply (curAt_fractional (GF := GF) (γ.withPhys p1) o1).fractional _ _ |>.2; iframe Hc1 Hc2
      iapply (revMuBody_fractional (GF := GF) s γ (γ.withPhys p1)).fractional q1 q2 |>.2
      iframe H1 H2

/-- **`s.revMu`'s resource** at fraction `q` (D22 receiver epochs, S3, 2026-10-22): half its
fraction of the restoring flag, at `m`, and the resource at the current physical names
(`revMuCur`, `m = false`; S5b) or, while `store.Restore` restores, its parts of the counters
(`revMuRest`, `m = true`). -/
def revMuInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ m : Bool, dghostVar γ.rst (DFrac.own q.half) m ∗
    (if m then revMuRest s q else revMuCur s γ q))

instance revMuInv_fractional (s : Loc) (γ : StoreNames) : Fractional (revMuInv (GF := GF) s γ) where
  fractional q1 q2 := by
    have hb := (revMuCur_fractional (GF := GF) s γ).fractional q1 q2
    have hr := (revMuRest_fractional (GF := GF) s).fractional q1 q2
    unfold revMuInv
    rw [Qp_half_add]
    constructor
    · iintro ⟨%m, Hf, H⟩
      icases (dghostVar_fractional (GF := GF) γ.rst m).fractional q1.half q2.half |>.1 $$ Hf
        with ⟨Hf1, Hf2⟩
      cases m
      · simp only [Bool.false_eq_true, ↓reduceIte] at *
        icases hb.1 $$ H with ⟨H1, H2⟩
        isplitl [Hf1 H1]
        · iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe Hf1 H1
        · iexists false; simp only [Bool.false_eq_true, ↓reduceIte]; iframe Hf2 H2
      · simp only [↓reduceIte] at *
        icases hr.1 $$ H with ⟨H1, H2⟩
        isplitl [Hf1 H1]
        · iexists true; simp only [↓reduceIte]; iframe Hf1 H1
        · iexists true; simp only [↓reduceIte]; iframe Hf2 H2
    · iintro ⟨⟨%m1, Hf1, H1⟩, ⟨%m2, Hf2, H2⟩⟩
      icombine Hf1 Hf2 gives %Hm
      obtain ⟨-, rfl⟩ := Hm
      iexists m1
      isplitl [Hf1 Hf2]
      · iapply (dghostVar_fractional (GF := GF) γ.rst m1).fractional q1.half q2.half |>.2
        iframe Hf1 Hf2
      cases m1
      · simp only [Bool.false_eq_true, ↓reduceIte] at *
        iapply hb.2; iframe H1 H2
      · simp only [↓reduceIte] at *
        iapply hr.2; iframe H1 H2

/-- **What closes `s.revMu`'s resource** at the physical names `γp` (S5b): half its fraction of the
restoring flag, down, an eighth of the current objects and names at `γp`'s, which are `γ`'s
logical names at physical ones. -/
def revMuTok (γ γp : StoreNames) (q : Qp) : IProp GF :=
  iprop(dghostVar γ.rst (DFrac.own q.half) false ∗
    (∃ o : StoreObjs, curAt γp (DFrac.own q.half.half.half) o) ∗ ⌜γp = γ.withPhys γp.phys⌝)

/-- **`s.revMu`'s resource, not restoring**: a part of the restoring flag down (a holder of `s.mu`'s
or a watchable store's share of the fields) finds the lock's body, at some physical names. -/
theorem revMuInv_open (s : Loc) (γ : StoreNames) (q : Qp) (dq : DFrac) :
    revMuInv (GF := GF) s γ q ∗ dghostVar γ.rst dq false ⊢
      (∃ γp : StoreNames, revMuBody s γ γp q ∗ revMuTok γ γp q) ∗ dghostVar γ.rst dq false := by
  unfold revMuInv
  iintro ⟨⟨%m, Hf, H⟩, Hr⟩
  icombine Hf Hr gives %Hm
  obtain ⟨-, rfl⟩ := Hm
  simp only [Bool.false_eq_true, ↓reduceIte]
  iunfold revMuCur at H
  icases H with ⟨%p, %o, Hc, H⟩
  iframe Hr
  iexists (γ.withPhys p)
  iframe H
  iunfold revMuTok
  iframe Hf
  isplitl
  · iexists o; iexact Hc
  ipureintro; rfl

/-- **`s.revMu`'s resource, not restoring, at the current names** (S5b): with a part of the
current objects and names at `γ.withPhys p`'s, the lock's body is at them. -/
theorem revMuInv_open_pin (s : Loc) (γ : StoreNames) (p : PhysNames) (q : Qp) (dq dq' : DFrac)
    (o : StoreObjs) :
    revMuInv (GF := GF) s γ q ∗ dghostVar γ.rst dq false ∗ curAt (γ.withPhys p) dq' o ⊢
      revMuBody s γ (γ.withPhys p) q ∗ revMuTok γ (γ.withPhys p) q ∗ dghostVar γ.rst dq false ∗
        curAt (γ.withPhys p) dq' o := by
  unfold revMuInv
  iintro ⟨⟨%m, Hf, H⟩, Hr, Hpin⟩
  icombine Hf Hr gives %Hm
  obtain ⟨-, rfl⟩ := Hm
  simp only [Bool.false_eq_true, ↓reduceIte]
  iunfold revMuCur at H
  icases H with ⟨%p', %o', Hc, H⟩
  ihave %Hv := curAt_withPhys_agree γ p' p _ _ o' o $$ [Hc Hpin]
  · iframe Hc Hpin
  obtain ⟨rfl, rfl⟩ := Hv
  iframe H Hr Hpin
  iunfold revMuTok
  iframe Hf
  isplitl
  · iexists o'; iexact Hc
  ipureintro; rfl

/-- `revMuInv_open_pin` at the current names `γ` themselves (the writer's, a compaction's). -/
theorem revMuInv_open_cur (s : Loc) (γ : StoreNames) (q : Qp) (dq dq' : DFrac) (o : StoreObjs) :
    revMuInv (GF := GF) s γ q ∗ dghostVar γ.rst dq false ∗ curAt γ dq' o ⊢
      revMuBody s γ γ q ∗ revMuTok γ γ q ∗ dghostVar γ.rst dq false ∗ curAt γ dq' o :=
  revMuInv_open_pin s γ γ.phys q dq dq' o

theorem revMuInv_close (s : Loc) (γ γp : StoreNames) (q : Qp) :
    revMuBody (GF := GF) s γ γp q ∗ revMuTok γ γp q ⊢ revMuInv s γ q := by
  unfold revMuInv revMuTok
  iintro ⟨H, Hf, ⟨%o, Hc⟩, %Hp⟩
  iexists false
  simp only [Bool.false_eq_true, ↓reduceIte]
  iframe Hf
  iunfold revMuCur
  iexists γp.phys, o
  rw [← Hp]
  iframe H Hc

/-- The initial log's bucket is empty. -/
theorem bucketMap_init : bucketMap [[], []] = (∅ : Bucket) := by
  simp [bucketMap, bucketOf, bucketOfRev]; rfl

/-- **The four fields `store.Restore` writes, at the objects `o`**, at the fraction `dq`
(D22 receiver epochs, S3: until then `↦□` in `isStore`). -/
def storeFields (s : Loc) (o : StoreObjs) (dq : DFrac) : IProp GF :=
  iprop("Hfb" ∷ (s.[store, go!"b"] ↦{dq} o.b : IProp GF) ∗
    "Hfidx" ∷ (s.[store, go!"kvindex"] ↦{dq}
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #o.ti : GoInterface) : IProp GF) ∗
    "Hfsch" ∷ (s.[store, go!"fifoSched"] ↦{dq} o.ssched : IProp GF) ∗
    "Hfstop" ∷ (s.[store, go!"stopc"] ↦{dq} o.sstop : IProp GF))

instance storeFields_persistent (s : Loc) (o : StoreObjs) :
    Persistent (storeFields (GF := GF) s o DFrac.discard) := by
  unfold storeFields; simp only [named]; infer_instance

theorem storeFields_split (s : Loc) (o : StoreObjs) (q1 q2 : Qp) :
    storeFields (GF := GF) s o (DFrac.own (q1 + q2)) ⊣⊢
      storeFields s o (DFrac.own q1) ∗ storeFields s o (DFrac.own q2) := by
  have hb : ∀ v : GoInterface, (s.[store, go!"b"] ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
      s.[store, go!"b"] ↦{DFrac.own q1} v ∗ s.[store, go!"b"] ↦{DFrac.own q2} v :=
    fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1) (DFrac.own q2)
  have hi : ∀ v : GoInterface, (s.[store, go!"kvindex"] ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
      s.[store, go!"kvindex"] ↦{DFrac.own q1} v ∗ s.[store, go!"kvindex"] ↦{DFrac.own q2} v :=
    fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1) (DFrac.own q2)
  have hs : ∀ v : GoInterface, (s.[store, go!"fifoSched"] ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
      s.[store, go!"fifoSched"] ↦{DFrac.own q1} v ∗ s.[store, go!"fifoSched"] ↦{DFrac.own q2} v :=
    fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1) (DFrac.own q2)
  have ht : ∀ v : Loc, (s.[store, go!"stopc"] ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
      s.[store, go!"stopc"] ↦{DFrac.own q1} v ∗ s.[store, go!"stopc"] ↦{DFrac.own q2} v :=
    fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1) (DFrac.own q2)
  unfold storeFields
  simp only [named]
  constructor
  · iintro ⟨Hb, Hi, Hs, Ht⟩
    icases (hb _).1 $$ Hb with ⟨Hb1, Hb2⟩
    icases (hi _).1 $$ Hi with ⟨Hi1, Hi2⟩
    icases (hs _).1 $$ Hs with ⟨Hs1, Hs2⟩
    icases (ht _).1 $$ Ht with ⟨Ht1, Ht2⟩
    iframe Hb1 Hi1 Hs1 Ht1 Hb2 Hi2 Hs2 Ht2
  · iintro ⟨⟨Hb1, Hi1, Hs1, Ht1⟩, ⟨Hb2, Hi2, Hs2, Ht2⟩⟩
    isplitl [Hb1 Hb2]
    · iapply (hb _).2; iframe Hb1 Hb2
    isplitl [Hi1 Hi2]
    · iapply (hi _).2; iframe Hi1 Hi2
    isplitl [Hs1 Hs2]
    · iapply (hs _).2; iframe Hs1 Hs2
    iapply (ht _).2; iframe Ht1 Ht2

/-- **What the store's objects `o` are at its names `γ`** (persistent; D22 receiver epochs, S5b:
until then `isStore`'s, at the pinned objects): the backend's contract at `γ`'s view, tokens, put
condition and lock resource, with the batch lock's invariant recorded (`hookP`) and the deposit
witness; the tree index; the scheduler. A share of the fields holds it of the current objects
and names (`fieldShareAt`), and so does the compaction's `storeStop`. (D22 receiver epochs, S6: the
store's registration in its backend, `storeRegd`, moved to the writer's invariant, `writerInv`: a
restored backend is registered only at its first writer's lock.) -/
def physOk (s : Loc) (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(∃ (Ph Dep : IProp GF),
    "#Hhook" ∷ hookP γ Ph ∗
    "#Hbk" ∷ isKeyBackendG o.b (bucketView γ) (storeRT γ) (storeWT γ) (kbNoCmp γ.kb γ.bucket)
      (storePutOk γ) (delKey γ)
      (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) Ph (hookFn γ) (storeReq γ) (storeRb γ) (storeBt γ)
      (MW := kbMW γ.kb) ∗
    "#Hdep" ∷ □ Dep ∗
    "#Hti" ∷ isTreeIndex o.ti γ.idx ∗
    "#HisSched" ∷ schedule.isFifo o.ssched γ.sch)

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 800000 in
instance physOk_persistent (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    Persistent (physOk (GF := GF) s γ o) := by
  unfold physOk; simp only [named]; infer_instance

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

theorem fieldShareAt_split (s : Loc) (γ : StoreNames) (q1 q2 : Qp) (o : StoreObjs) :
    fieldShareAt (GF := GF) s γ (q1 + q2) o ⊣⊢ fieldShareAt s γ q1 o ∗ fieldShareAt s γ q2 o := by
  have hr := (dghostVar_fractional (GF := GF) γ.rst false).fractional q1.half q2.half
  have hc := (curAt_fractional (GF := GF) γ o).fractional q1.half q2.half
  unfold fieldShareAt
  rw [Qp_half_add]
  constructor
  · iintro ⟨Hc, H, Hr, #Hph⟩
    icases (storeFields_split s o q1 q2).1 $$ H with ⟨H1, H2⟩
    icases hr.1 $$ Hr with ⟨Hr1, Hr2⟩
    icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
    simp only [named]
    isplitl [H1 Hr1 Hc1]
    · iframe Hc1 H1 Hr1 Hph
    · iframe Hc2 H2 Hr2 Hph
  · iintro ⟨⟨Hc1, H1, Hr1, #Hph⟩, ⟨Hc2, H2, Hr2, -⟩⟩
    simp only [named]
    iframe Hph
    isplitl [Hc1 Hc2]
    · iapply hc.2; iframe Hc1 Hc2
    isplitl [H1 H2]
    · iapply (storeFields_split s o q1 q2).2; iframe H1 H2
    iapply hr.2; iframe Hr1 Hr2

instance fieldShare_fractional (s : Loc) (γ : StoreNames) : Fractional (fieldShare (GF := GF) s γ) where
  fractional q1 q2 := by
    unfold fieldShare
    constructor
    · iintro ⟨%p, %o, H⟩
      icases (fieldShareAt_split s _ q1 q2 o).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists p, o; iexact H1
      · iexists p, o; iexact H2
    · iintro ⟨⟨%p1, %o1, H1⟩, ⟨%p2, %o2, H2⟩⟩
      iunfold fieldShareAt at H1 H2
      icases H1 with ⟨Hc1, H1⟩
      icases H2 with ⟨Hc2, H2⟩
      ihave %Hv := curAt_withPhys_agree γ p1 p2 _ _ o1 o2 $$ [Hc1 Hc2]
      · iframe Hc1 Hc2
      obtain ⟨rfl, rfl⟩ := Hv
      iexists p1, o1
      iapply (fieldShareAt_split s _ q1 q2 o1).2
      iunfold fieldShareAt
      iframe Hc1 Hc2 H1 H2

/-- A share at the current names `γ` (`p := γ.phys`). -/
theorem fieldShare_of_at (s : Loc) (γ : StoreNames) (q : Qp) (o : StoreObjs) :
    fieldShareAt (GF := GF) s γ q o ⊢ fieldShare s γ q := by
  iintro H
  iunfold fieldShare
  iexists γ.phys, o
  rw [StoreNames.withPhys_self]
  iexact H

/-- **A share, at a pin**: with a part of the current objects and names at `γ`'s, the share is at
them. -/
theorem fieldShare_pin (s : Loc) (γ : StoreNames) (q : Qp) (dq : DFrac) (o : StoreObjs) :
    curAt (GF := GF) γ dq o ∗ fieldShare s γ q ⊢ curAt γ dq o ∗ fieldShareAt s γ q o := by
  iintro ⟨Hpin, H⟩
  iunfold fieldShare at H
  icases H with ⟨%p, %o', H⟩
  iunfold fieldShareAt at H
  icases H with ⟨Hc, H⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iframe Hpin
  iunfold fieldShareAt
  iframe Hc H

/-- A share's part of the current objects and names, lent (a pin for the share's holder). -/
theorem fieldShareAt_cur (s : Loc) (γ : StoreNames) (q : Qp) (o : StoreObjs) :
    fieldShareAt (GF := GF) s γ q o ⊢
      curAt γ (DFrac.own q.half) o ∗ (curAt γ (DFrac.own q.half) o -∗ fieldShareAt s γ q o) := by
  iintro H
  iunfold fieldShareAt at H
  iNamed H
  iframe Hcur
  iintro Hcur
  iunfold fieldShareAt
  iframe Hcur Hflds Hfrst Hph

/-- What a share's objects are (persistent). -/
theorem fieldShareAt_phys (s : Loc) (γ : StoreNames) (q : Qp) (o : StoreObjs) :
    fieldShareAt (GF := GF) s γ q o ⊢ □ physOk s γ o := by
  iintro H
  iunfold fieldShareAt at H
  iNamed H
  iexact Hph

/-- A share's `kvindex`, lent. -/
theorem fieldShareAt_idx (s : Loc) (γ : StoreNames) (q : Qp) (o : StoreObjs) :
    fieldShareAt (GF := GF) s γ q o ⊢
      (s.[store, go!"kvindex"] ↦{DFrac.own q} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #o.ti : GoInterface) : IProp GF) ∗
      ((s.[store, go!"kvindex"] ↦{DFrac.own q} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #o.ti : GoInterface) : IProp GF) -∗
        fieldShareAt s γ q o) := by
  iintro H
  iunfold fieldShareAt at H
  iNamed H
  iunfold storeFields at Hflds
  iNamed Hflds
  iframe Hfidx
  iintro Hfidx
  iunfold fieldShareAt
  simp only [named]
  iframe Hcur Hfrst Hph
  iunfold storeFields
  simp only [named]
  iframe Hfb Hfidx Hfsch Hfstop

/-- The number of reader slots of the store's locks (`NewStore` hands out one reader per slot). -/
abbrev nReaders : Nat := Int.toNat sync.rwmutex.actualMaxReaders

/-- **A slot of the readers' pool** (D22 receiver epochs, S4, 2026-10-22; S5a: with the backend's
reader token): a reader slot of the store's index's lock (of the objects `o`'s index; S5b: the
current one, `readerPool`), and a reader token of the store's backend (`storeRT`: until S5a each reader held its own, so
a restore, which swaps the backend, could not hand out the new one's nor take the old ones back
for the old backend's `Close`). -/
def idxSlot (γ : StoreNames) (o : StoreObjs) : IProp GF :=
  iprop(idxReader o.ti γ.idx ∗ storeRT γ)

/-- The slots of the index's lock, with the backend's reader tokens, as the readers' pool's (D22
receiver epochs, S4; S5a: with the tokens; S5b: of the objects `o`). -/
theorem idxSlots_of (γ : StoreNames) (o : StoreObjs) : ∀ (n : Nat),
    ([∗list] _x ∈ List.replicate n (), idxReader (GF := GF) o.ti γ.idx) ∗
      ([∗list] _x ∈ List.replicate n (), storeRT γ) ⊢
      [∗list] _x ∈ List.replicate n (), idxSlot γ o
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨Hi, Ht⟩
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨Hi1, Hi⟩
    icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Ht1, Ht⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hi1 Ht1]
    · iunfold idxSlot; iframe Hi1 Ht1
    · iapply idxSlots_of γ o n; iframe Hi Ht

/-- **The watchable store's deposit** (D22 receiver epochs, S5a): all of the watchable store's
deposit ghost (`StoreNames.wsd`, held by the watchable store's `s.mu` at its fraction,
`wsFields`): `syncWatchers`, holding that lock exclusively, deposits it in the readers' pool while
it has a slot out. -/
def wsDep (γ : StoreNames) : IProp GF := ghostVar γ.wsd 1 ()

/-- The readers' pool's invariant name. -/
abbrev poolN : Namespace := nroot.@"mvcc_readers"

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

/-- **The readers' pool's retired count is `r`** (D22 receiver epochs, S8d, W7, 2026-10-25; the
store's creator's half of `γ.tkr`, `NewStore` gives it at `0`): each retirement
(`readerPool_retire`) counts one. -/
def retiredAt (γ : StoreNames) (r : Nat) : IProp GF := ghostVar γ.tkr (1 : Qp).half r

instance retiredAt_timeless (γ : StoreNames) (r : Nat) : Timeless (retiredAt (GF := GF) γ r) := by
  unfold retiredAt; infer_instance

/-- The readers' pool's invariant (S5b): its body at the current objects and names, with an eighth
of the fraction of them. -/
def readerPool (γ : StoreNames) : IProp GF :=
  inv poolN iprop(∃ (p : PhysNames) (o : StoreObjs),
    curAt (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗ poolBody (γ.withPhys p) o)

instance readerPool_persistent (γ : StoreNames) : Persistent (readerPool (GF := GF) γ) := by
  unfold readerPool; infer_instance

/-- `s.mu`'s resource at fraction `q`, at the compaction revision `c` (`-1`: none): half
`compactMainRev`'s points-to and a quarter of the compaction revision's authority (`s.revMu`
holds as much; the compaction right, half the authority, is `compactRight`), with a certified
log of which `c` is a revision, safe for readers (`crevSafe`: no key deleted then put again at
`c`, which `store.Compact`'s caller asserts; 2026-10-13, unit 6a). A transaction holds `s.mu`
shared for its whole life, so its `rangeKeys` reads `compactMainRev` from its part (`muHeld`). -/
def muInvAt (s : Loc) (γ : StoreNames) (q : Qp) (c : Int) : IProp GF :=
  iprop("HcmpM" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 c : w64) : IProp GF) ∗
    "HcrevM" ∷ crevUB γ.idx q.half.half c ∗
    "#HclM" ∷ crevSafe γ c ∗
    "%HcM" ∷ ⌜-1 ≤ c⌝)

/-- `s.mu`'s resource at fraction `q`: at some compaction revision, and the writer's deposit
ghost at the fraction (D22 receiver epochs, S2: a holder of `s.mu` exclusively has all of it, so
no writer has the writer's state out, `writerInv`). -/
def muInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ c : Int, muInvAt s γ q c ∗ ghostVar γ.wr q () ∗ fieldShare s γ q.half)

instance muInv_fractional (s : Loc) (γ : StoreNames) : Fractional (muInv (GF := GF) s γ) where
  fractional q1 q2 := by
    have hcmp : ∀ v : w64, (s.[store, go!"compactMainRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"compactMainRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"compactMainRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hcrev := fun (c : Int) => crevUB_split (GF := GF) γ.idx q1.half.half q2.half.half c
    have hwr := (ghostVar_fractional (GF := GF) γ.wr ()).fractional q1 q2
    have hfs := (fieldShare_fractional (GF := GF) s γ).fractional q1.half q2.half
    unfold muInv muInvAt
    rw [Qp_half_add, Qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro H
      icases H with ⟨%c, H, Hwr, Hfs⟩
      iNamed H
      icases (hcmp _).1 $$ HcmpM with ⟨Hm1, Hm2⟩
      icases (hcrev c).1 $$ HcrevM with ⟨Hv1, Hv2⟩
      icases hwr.1 $$ Hwr with ⟨Hw1, Hw2⟩
      icases hfs.1 $$ Hfs with ⟨Hf1, Hf2⟩
      isplitl [Hm1 Hv1 Hw1 Hf1]
      · iexists c; simp only [named]; iframe Hm1 Hv1 Hw1 Hf1; iframe #; ipureintro; exact HcM
      · iexists c; simp only [named]; iframe Hm2 Hv2 Hw2 Hf2; iframe #; ipureintro; exact HcM
    · iintro ⟨H1, H2⟩
      icases H1 with ⟨%c, H1, Hw1, Hf1⟩
      icases H2 with ⟨%c2, H2, Hw2, Hf2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      ihave %Hcc := crevUB_agree γ.idx _ _ c c2 HcM1 HcM2 $$ HcrevM1 HcrevM2
      subst Hcc
      iexists c
      isplitr [Hw1 Hw2 Hf1 Hf2]
      rotate_left
      · isplitl [Hw1 Hw2]
        · iapply hwr.2; iframe Hw1 Hw2
        iapply hfs.2; iframe Hf1 Hf2
      simp only [named]
      isplitl [HcmpM1 HcmpM2]
      · iapply (hcmp _).2; iframe HcmpM1 HcmpM2
      isplitl [HcrevM1 HcrevM2]
      · iapply (hcrev c).2; iframe HcrevM1 HcrevM2
      isplitr
      · iexact HclM1
      ipureintro; exact HcM1

/-- `s.mu` held shared by a transaction, at the compaction revision `c`: the reader's token and
its part of `s.mu`'s resource (given back at `End`), its share of the fields at the current
objects, whose index is `ti`, and names, `γ`'s (D22 receiver epochs, S5b: a transaction is at the
names its `s.mu` share pins; until then the index's pin `idxPin`). -/
def muHeld (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) : IProp GF :=
  iprop(sync.ownRWMutexRLocked (muAddr s) (muInv s γ) ∗ muInvAt s γ sync.rfrac c ∗
    ∃ o : StoreObjs, ⌜o.ti = ti⌝ ∗ fieldShareAt s γ sync.rfrac.half o)

/-- A transaction's part of the store's `kvindex`, lent (D22 receiver epochs, S3: until then `↦□`
in `isStore`). -/
theorem muHeld_idx (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢
      (s.[store, go!"kvindex"] ↦{DFrac.own sync.rfrac.half} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) ∗
      ((s.[store, go!"kvindex"] ↦{DFrac.own sync.rfrac.half} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) -∗
        muHeld s γ c ti) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, %o, %Ho, Hf⟩
  subst Ho
  icases fieldShareAt_idx s γ _ o $$ Hf with ⟨Hi, Hb⟩
  iframe Hi
  iintro Hi
  ihave Hf := Hb $$ Hi
  iunfold muHeld
  iframe Hl Ha
  iexists o
  iframe Hf
  ipureintro; rfl

/-- **What a transaction's objects are** (persistent): of the objects whose index is `ti`, at
`γ`'s names (S5b: until then `isStore`'s). -/
theorem muHeld_phys (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢ ∃ o : StoreObjs, ⌜o.ti = ti⌝ ∗ □ physOk s γ o := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨-, -, %o, %Ho, Hf⟩
  ihave #Hph := fieldShareAt_phys s γ _ o $$ Hf
  iexists o
  iframe Hph
  ipureintro; exact Ho

/-- A transaction's tree index, keeping the transaction. -/
theorem muHeld_tree (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢ muHeld s γ c ti ∗ isTreeIndex ti γ.idx := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, %o, %Ho, Hf⟩
  iunfold fieldShareAt at Hf
  iNamed Hf
  ihave #Hph' := Hph
  iunfold physOk at Hph'
  iNamed Hph'
  subst Ho
  iframe Hti
  iunfold muHeld
  iframe Hl Ha
  iexists o
  isplitl []
  · ipureintro; rfl
  iunfold fieldShareAt
  iframe Hcur Hflds Hfrst Hph

/-- **A transaction's pin** (S5b): its part of the current objects and names, lent. -/
theorem muHeld_cur (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢ ∃ o : StoreObjs, ⌜o.ti = ti⌝ ∗
      curAt γ (DFrac.own sync.rfrac.half.half) o ∗
      (curAt γ (DFrac.own sync.rfrac.half.half) o -∗ muHeld s γ c ti) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, %o, %Ho, Hf⟩
  icases fieldShareAt_cur s γ _ o $$ Hf with ⟨Hc, Hb⟩
  iexists o
  iframe Hc
  isplitl []
  · ipureintro; exact Ho
  iintro Hc
  ihave Hf := Hb $$ Hc
  iunfold muHeld
  iframe Hl Ha
  iexists o
  iframe Hf
  ipureintro; exact Ho

/-- A transaction's part of the compaction revision's authority, lent (to the index's reads). -/
theorem muHeld_crev (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢
      crevUB γ.idx sync.rfrac.half.half c ∗ (crevUB γ.idx sync.rfrac.half.half c -∗ muHeld s γ c ti) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, Hf⟩
  iunfold muInvAt at Ha
  iNamed Ha
  iframe HcrevM
  iintro Hc
  iunfold muHeld
  iframe Hl Hf
  iunfold muInvAt
  iframe HcmpM Hc
  iframe #
  ipureintro; exact HcM

/-- A transaction's part of `compactMainRev` and of the compaction revision's authority, lent (to
`rangeKeys`), with the revision's bounds. -/
theorem muHeld_cmp (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢
      (s.[store, go!"compactMainRev"] ↦{DFrac.own sync.rfrac.half} (W64 c : w64) : IProp GF) ∗
      crevUB γ.idx sync.rfrac.half.half c ∗ ⌜-1 ≤ c ∧ c < 2 ^ 63⌝ ∗
      ((s.[store, go!"compactMainRev"] ↦{DFrac.own sync.rfrac.half} (W64 c : w64) : IProp GF) -∗
        crevUB γ.idx sync.rfrac.half.half c -∗ muHeld s γ c ti) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, Hf⟩
  iunfold muInvAt at Ha
  iNamed Ha
  ihave #Hcl := HclM
  iunfold crevSafe at Hcl
  icases Hcl with ⟨%log₀, #Hc0, %Hlt⟩
  iunfold idxCert at Hc0
  icases Hc0 with ⟨-, %Hwf, -⟩
  iframe HcmpM HcrevM
  isplitl []
  · ipureintro; exact ⟨HcM, by have := Hlt.1; omega⟩
  iintro Hm Hc
  iunfold muHeld
  iframe Hl Hf
  iunfold muInvAt
  iframe Hm Hc
  iframe #
  ipureintro; exact HcM

/-- **A transaction holding `s.mu` finds `s.revMu`'s resource not restoring**, at its names (its
part of the fields' share has the restoring flag down and pins the current names; D22 receiver
epochs, S3, S5b). -/
theorem revMuInv_open_held (s : Loc) (γ : StoreNames) (q : Qp) (c : Int) (ti : Loc) :
    revMuInv (GF := GF) s γ q ∗ muHeld s γ c ti ⊢
      revMuBody s γ γ q ∗ revMuTok γ γ q ∗ muHeld s γ c ti := by
  iintro ⟨H, Hm⟩
  iunfold muHeld at Hm
  icases Hm with ⟨Hl, Ha, %o, %Ho, Hf⟩
  iunfold fieldShareAt at Hf
  iNamed Hf
  icases revMuInv_open_cur s γ q _ _ o $$ [H Hfrst Hcur] with ⟨H, Htk, Hfrst, Hcur⟩
  · iframe H Hfrst Hcur
  iframe H Htk
  iunfold muHeld
  iframe Hl Ha
  iexists o
  isplitl []
  · ipureintro; exact Ho
  iunfold fieldShareAt
  iframe Hcur Hflds Hfrst Hph

/-- A transaction's part of the compaction revision's authority and of the store's `kvindex`,
lent (to the index's reads; D22 receiver epochs, S3). -/
theorem muHeld_crev_idx (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢
      crevUB γ.idx sync.rfrac.half.half c ∗
      (s.[store, go!"kvindex"] ↦{DFrac.own sync.rfrac.half} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) ∗
      (crevUB γ.idx sync.rfrac.half.half c -∗
        (s.[store, go!"kvindex"] ↦{DFrac.own sync.rfrac.half} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) -∗
        muHeld s γ c ti) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, %o, %Ho, Hf⟩
  subst Ho
  icases fieldShareAt_idx s γ _ o $$ Hf with ⟨Hi, Hfb⟩
  iunfold muInvAt at Ha
  iNamed Ha
  iframe HcrevM Hi
  iintro Hc Hi
  ihave Hf := Hfb $$ Hi
  iunfold muHeld
  iframe Hl
  isplitr [Hf]
  · iunfold muInvAt
    iframe HcmpM Hc
    iframe #
    ipureintro; exact HcM
  iexists o
  iframe Hf
  ipureintro; rfl

/-- A transaction's part of `compactMainRev`, of the compaction revision's authority and of the
store's `kvindex`, lent (to `rangeKeys`; D22 receiver epochs, S3). -/
theorem muHeld_cmp_idx (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) :
    muHeld (GF := GF) s γ c ti ⊢
      (s.[store, go!"compactMainRev"] ↦{DFrac.own sync.rfrac.half} (W64 c : w64) : IProp GF) ∗
      crevUB γ.idx sync.rfrac.half.half c ∗ ⌜-1 ≤ c ∧ c < 2 ^ 63⌝ ∗
      (s.[store, go!"kvindex"] ↦{DFrac.own sync.rfrac.half} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) ∗
      ((s.[store, go!"compactMainRev"] ↦{DFrac.own sync.rfrac.half} (W64 c : w64) : IProp GF) -∗
        crevUB γ.idx sync.rfrac.half.half c -∗
        (s.[store, go!"kvindex"] ↦{DFrac.own sync.rfrac.half} (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) -∗
        muHeld s γ c ti) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, %o, %Ho, Hf⟩
  subst Ho
  icases fieldShareAt_idx s γ _ o $$ Hf with ⟨Hi, Hfb⟩
  iunfold muInvAt at Ha
  iNamed Ha
  ihave #Hcl := HclM
  iunfold crevSafe at Hcl
  icases Hcl with ⟨%log₀, #Hc0, %Hlt⟩
  iunfold idxCert at Hc0
  icases Hc0 with ⟨-, %Hwf, -⟩
  iframe HcmpM HcrevM Hi
  isplitl []
  · ipureintro; exact ⟨HcM, by have := Hlt.1; omega⟩
  iintro Hm Hc Hi
  ihave Hf := Hfb $$ Hi
  iunfold muHeld
  iframe Hl
  isplitr [Hf]
  · iunfold muInvAt
    iframe Hm Hc
    iframe #
    ipureintro; exact HcM
  iexists o
  iframe Hf
  ipureintro; rfl

/-- A store (persistent): its lessor, logger, and the two locks' guards; and what compaction uses:
the configuration (a positive `CompactionBatchLimit`: the job's loop needs it to end,
`issues/etcd-compaction-negative-batch-limit.md`), the hash storage. **Nothing of its objects and
physical names** (D22 receiver epochs, S5b, 2026-10-22: until then the backend of its instance
`γ.kb`, registered, with the batch lock's deposit witness, the batch lock's invariant `hookP`, the
index, the scheduler, at the pinned objects): they are the current ones, which `store.Restore`
replaces, so they are in the shares of the locks guarding their readers (`fieldShareAt`'s
`physOk`, at a part of the store's current objects and names, `curAt`), and `isStore s γ` reads
only `γ`'s logical names (`isStore_withPhys`). **The four fields `store.Restore` writes** (`b`,
`kvindex`, `fifoSched`, `stopc`) are not here either (S3: until then `↦□`): their points-to are
shared by the locks (`fieldShare`). That the scheduler is never stopped (`schedLive`) is not the
store's but the compaction's (`compactRight`, `compactJobPre`), since `NewStore` returns the stop
token for its caller to give up only once the store will not be closed (D19m (C), 2026-10-18:
`storeCloser`). The fields `restore` and `Close` change are fixed here (out of scope).
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
    "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
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

/-- **A store reads only its logical names** (D22 receiver epochs, S5b). -/
theorem isStore_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) :
    isStore (GF := GF) s (γ.withPhys p) = isStore s γ := rfl

theorem crevFrozen_withPhys (γ : StoreNames) (p : PhysNames) :
    crevFrozen (GF := GF) (γ.withPhys p) = crevFrozen γ := rfl

theorem revMuInv_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) :
    revMuInv (GF := GF) s (γ.withPhys p) = revMuInv s γ := rfl

theorem idxCert_withPhys (γ : StoreNames) (p : PhysNames) (L : Log) :
    idxCert (GF := GF) (γ.withPhys p).idx L = idxCert γ.idx L := rfl

theorem idxSealed_withPhys (γ : StoreNames) (p : PhysNames) (L : Log) :
    idxSealed (GF := GF) (γ.withPhys p).idx L = idxSealed γ.idx L := rfl

theorem idxLogAuth_withPhys (γ : StoreNames) (p : PhysNames) (q : Qp) (L : Log) :
    idxLogAuth (GF := GF) (γ.withPhys p).idx q L = idxLogAuth γ.idx q L := rfl

theorem crevUB_withPhys (γ : StoreNames) (p : PhysNames) (q : Qp) (c : Int) :
    crevUB (GF := GF) (γ.withPhys p).idx q c = crevUB γ.idx q c := rfl

theorem crevLb_withPhys (γ : StoreNames) (p : PhysNames) (c : Int) :
    crevLb (GF := GF) (γ.withPhys p).idx c = crevLb γ.idx c := rfl

theorem crevSafe_withPhys (γ : StoreNames) (p : PhysNames) (c : Int) :
    crevSafe (GF := GF) (γ.withPhys p) c = crevSafe γ c := rfl

theorem muInvAt_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) (q : Qp) (c : Int) :
    muInvAt (GF := GF) s (γ.withPhys p) q c = muInvAt s γ q c := rfl

theorem certOk_withPhys (γ : StoreNames) (p : PhysNames) (L : Log) :
    certOk (GF := GF) (γ.withPhys p) L = certOk γ L := rfl

theorem delKey_withPhys (γ : StoreNames) (p : PhysNames) :
    delKey (GF := GF) (γ.withPhys p) = delKey γ := rfl

theorem revToken_withPhys (γ : StoreNames) (p : PhysNames) :
    revToken (GF := GF) (γ.withPhys p) = revToken γ := rfl

theorem muInv_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) :
    muInv (GF := GF) s (γ.withPhys p) = muInv s γ := rfl

theorem writerInv_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) :
    writerInv (GF := GF) s (γ.withPhys p) = writerInv s γ := rfl

theorem readerPool_withPhys (γ : StoreNames) (p : PhysNames) :
    readerPool (GF := GF) (γ.withPhys p) = readerPool γ := rfl

theorem wDep_withPhys (γ : StoreNames) (p : PhysNames) :
    wDep (GF := GF) (γ.withPhys p) = wDep γ := rfl

theorem wsDep_withPhys (γ : StoreNames) (p : PhysNames) :
    wsDep (GF := GF) (γ.withPhys p) = wsDep γ := rfl

/-- **The store's backend contract** (what `NewStore` takes, for every store of the instance):
`isKeyBackendG` at the store's view, tokens and put condition of its instance, its deletable keys
(`delKey`), its lock resource (`storeW`, initially `kbWi`), whether it supports the compaction
(`storeCmp`), the batch lock's invariant `P` and its post-lock hook as the store's names hold it
(`hookFn γ`: `LockInsideApply` runs the hook it is given the frozen fact of; unit N4, D14b: the
store's contract no longer fixes the hook, which the etcd server installs after the store),
with some deposit witness. -/
def storeBackend (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF) : IProp GF :=
  iprop(∃ Dep : IProp GF, isKeyBackendG b (bucketView γ) (storeRT γ) (storeWT γ)
    (kbNoCmp γ.kb γ.bucket) (storePutOk γ)
    (delKey γ) (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) P (hookFn γ) (storeReq γ) (storeRb γ) (storeBt γ)
    (MW := kbMW γ.kb))

instance storeBackend_persistent (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF) :
    Persistent (storeBackend (GF := GF) b s γ P) := by
  unfold storeBackend; infer_instance

/-- **The store's backend contract with the deposit witness `True`** (D22 receiver epochs, S6,
2026-10-22): `storeBackend` with its witness fixed, as the real backend's is
(`storeBackendT_of_backend`: its batch lock holds the late-bound resource from its creation, so no
first `Unlock` deposits it). What `store.Restore` takes of its new backend: it never locks the new
backend's batch transaction, so it has no witness of its own. -/
def storeBackendT (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF) : IProp GF :=
  isKeyBackendG b (bucketView γ) (storeRT γ) (storeWT γ) (kbNoCmp γ.kb γ.bucket) (storePutOk γ)
    (delKey γ) (storeW s γ)
    (kbWi γ.kb) iprop(True) (storeCmp γ) P (hookFn γ) (storeReq γ) (storeRb γ) (storeBt γ)
    (MW := kbMW γ.kb)

instance storeBackendT_persistent (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF) :
    Persistent (storeBackendT (GF := GF) b s γ P) := by
  unfold storeBackendT; infer_instance

/-- **The backend's `ReadTx` over a clean view** (the restore plan's R5a): from a share `View q m`
of a view whose read buffer is known clean, `ReadTx` then `RLock` read the bucket `m` itself, with
the limited range's prefix clause (`keyReadSnapC`). What `store.restore` takes of a backend holding
data (the real one's: `keyCleanRead_of_backend`). -/
def keyCleanRead (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT NC : IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnapC View RT NC rt m L }}))

instance keyCleanRead_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT NC : IProp GF) : Persistent (keyCleanRead (GF := GF) b View RT NC) := by
  unfold keyCleanRead; infer_instance

/-- The contract with the witness `True` is the contract. -/
theorem storeBackend_of_T (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF) :
    storeBackendT (GF := GF) b s γ P ⊢ storeBackend b s γ P := by
  iintro #H
  iunfold storeBackendT at H
  iunfold storeBackend
  iexists iprop(True)
  iexact H

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 800000 in
instance isStore_persistent (s : Loc) (γ : StoreNames) : Persistent (isStore (GF := GF) s γ) := by
  unfold isStore; infer_instance

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

/-- **The store's reader** (a transaction's tokens: a reader slot of each of `s.mu` and `s.revMu`,
and a ticket of the readers' pool, whose slot has a reader's token of the backend: S5a), as the
txn, apply, request path and watchable store hold it: `storeReaderC`. Until M2
(`notes/m2-plan.md`, S1, 2026-10-27) it also carried `crevFrozen` (a store never compacted), and
the packages above mvcc used the store's specs through frozen corollaries (`FrozenSpecs.lean`,
removed); now they use the general specs, whose transactions observe the compaction revision. -/
def storeReader (s : Loc) (γ : StoreNames) : IProp GF := storeReaderC s γ

theorem storeReaderC_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) :
    storeReaderC (GF := GF) s (γ.withPhys p) = storeReaderC s γ := rfl

theorem storeReader_withPhys (s : Loc) (γ : StoreNames) (p : PhysNames) :
    storeReader (GF := GF) s (γ.withPhys p) = storeReader s γ := rfl

/-- A reader from the store's specs' reader. -/
theorem storeReader_of (s : Loc) (γ : StoreNames) :
    storeReaderC (GF := GF) s γ ⊢ storeReader s γ := by
  unfold storeReader; exact .rfl

/-- Readers from the store's specs' readers. -/
theorem storeReaders_of (s : Loc) (γ : StoreNames) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), storeReaderC (GF := GF) s γ) ⊢
      [∗list] _x ∈ List.replicate n (), storeReader s γ := by
  unfold storeReader; exact .rfl

/-- The store's specs' reader from a reader. -/
theorem storeReader_toC (s : Loc) (γ : StoreNames) :
    storeReader (GF := GF) s γ ⊢ storeReaderC s γ := by
  unfold storeReader; exact .rfl

/-- **The sole writer's own resources on the store's backend** (D22 receiver epochs, S5a,
2026-10-22): a reader token of the backend of its own (retired from the readers' pool,
`storeReader_retire`; until S5a a reader's handle had one), which its writes under the batch lock
borrow (the apply package's contracts: `apply.kvOwn`). A restore takes it back and gives the new
backend's. (The restore plan's R5e) With the readers' pool's retired count (D22 receiver epochs, S8d,
W7, 2026-10-25: `retiredAt γ 2`, until then the writer's retired ticket): the etcd server, the
store's only creator that retires, retires two readers (the storage version monitor's and the
writer's), so the restore knows the pool holds `nReaders - 2` slots, and returns exactly the old
backend's tokens it held. -/
def writerOwn (γ : StoreNames) : IProp GF := iprop(storeRT γ ∗ retiredAt γ 2)

/-- The sole writer lends its backend token. -/
theorem writerOwn_rt (γ : StoreNames) :
    writerOwn (GF := GF) γ ⊢ storeRT γ ∗ (storeRT γ -∗ writerOwn γ) := by
  unfold writerOwn
  iintro ⟨H, Ht⟩
  iframe H
  iintro H
  iframe H Ht

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
    "#Hsnap" ∷ keyReadLocked (storeRT γ) (kbNoCmp γ.kb γ.bucket) false rt m' Rd Tok ∗
    "#Hthin" ∷ snapThin m m' (delKey γ) ∗
    "Htok" ∷ Tok ∗
    "Hwr" ∷ wDep γ ∗
    "Htko" ∷ ownToks γ.tko 1 ∗
    "%Hsub" ∷ ⌜GMap.Subseteq (bucketMap log) m⌝)

instance storeTxnReadIs_persistent (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames)
    (log : Log) (rev : w64) (crev : Int) (Z : IProp GF) :
    Persistent (storeTxnReadIs (GF := GF) tr s rt trace γ log rev crev Z) := by
  unfold storeTxnReadIs; infer_instance

/-- The last revision of a certified log, not empty, is not negative. -/
theorem idxCert_lastRev (γ : StoreNames) (log : Log) (hne : log ≠ []) :
    idxCert (GF := GF) γ.idx log ⊢ ⌜0 ≤ sint.Z (W64 ((log.length : Int) - 1) : w64)⌝ := by
  iintro H
  iunfold idxCert at H
  icases H with ⟨-, %Hcwf, -⟩
  ipureintro
  have hpos : 0 < log.length := List.length_pos_iff.2 hne
  unfold sint.Z W64
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
    (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  omega

/-- A read transaction's revision is one of its log's. -/
theorem storeTxnReadIs_rev (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames)
    (log : Log) (rev : w64) (crev : Int) (Z : IProp GF) :
    storeTxnReadIs (GF := GF) tr s rt trace γ log rev crev Z ⊢
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < log.length⌝ := by
  iintro H
  iunfold storeTxnReadIs at H
  iNamed H
  iunfold idxCert at Hcert
  icases Hcert with ⟨-, %Hcwf, -⟩
  ipureintro
  have hpos : 0 < log.length := List.length_pos_iff.2 Hne
  rw [Hrev]; unfold sint.Z W64
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
    (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  omega

/-- **A read transaction's compaction revision is at most its revision** (M2, S1), and at least
`-1`. -/
theorem storeTxnReadIs_crev (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames)
    (log : Log) (rev : w64) (crev : Int) (Z : IProp GF) :
    storeTxnReadIs (GF := GF) tr s rt trace γ log rev crev Z ⊢
      ⌜-1 ≤ crev ∧ crev ≤ sint.Z rev⌝ := by
  iintro H
  iunfold storeTxnReadIs at H
  iNamed H
  iunfold idxCert at Hcert
  icases Hcert with ⟨-, %Hcwf, -⟩
  ipureintro
  have hpos : 0 < log.length := List.length_pos_iff.2 Hne
  have hr : sint.Z rev = (log.length : Int) - 1 := by
    rw [Hrev]; unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  omega

/-- The read transaction `store.Read` returns, as the caller sees it: the `metricsTxnWrite`
wrapper at `mw` (its counters), around the `txnReadWrite` wrapper around the `storeTxnRead`
(at the compaction revision `crev`, with the reader's tag `Z`: `storeTxnReadIs`; `Z` by default
`True`), with the transaction's tokens (`s.mu` held
shared until `End`, at `crev`) and its reader's (`txReader`), and the trace `trace` the
transaction steps (owned: `store.Read` takes it, `End` gives it back; a caller stepping the trace
meanwhile borrows it, `isTxn_trace_acc`). -/
def isTxnRead (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64) (crev : Int)
    (Z : IProp GF := iprop(True)) : IProp GF :=
  iprop(∃ (p : PhysNames) (trw tr ti : Loc) (rt : GoInterfaceOk) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw,
        ranges' := ranges, puts' := W64 0, deletes' := W64 0, putSize' := W64 0 } : metricsTxnWrite) ∗
    "Htrw" ∷ trw.[txnReadWrite, go!"TxnRead"] ↦
      (interface.mkOk (go.GoType.PointerType storeTxnRead.ty) #tr : GoInterface) ∗
    "#Hs" ∷ isStore s γ ∗
    "#Htr" ∷ storeTxnReadIs tr s rt trace (γ.withPhys p) log rev crev Z ∗
    "Hrd" ∷ txReader (γ.withPhys p) rt log ∗
    "Hmu" ∷ muHeld s (γ.withPhys p) crev ti ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti (γ.withPhys p).idx ∗
    "Htrc" ∷ (∃ te : Bool, traceutil.ownTrace trace te))

/-- **A read transaction's compaction revision is at most its revision** (M2, S1;
`storeTxnReadIs_crev`). -/
theorem isTxnRead_crev (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64)
    (crev : Int) (Z : IProp GF) :
    isTxnRead (GF := GF) mw s γ trace log rev crev Z ⊢ ⌜-1 ≤ crev ∧ crev ≤ sint.Z rev⌝ := by
  iintro H
  iunfold isTxnRead at H
  iNamed H
  iapply storeTxnReadIs_crev $$ Htr

/-- **A frozen reader observed no compaction**: with the frozen tag (`Z = crevFrozen γ`), the
transaction's compaction revision is `-1` (its part of the revision's authority agrees with the
frozen right's). -/
theorem muHeld_frozen (s : Loc) (γ : StoreNames) (crev : Int) (ti : Loc) :
    ⊢ crevFrozen (GF := GF) γ -∗ muHeld s γ crev ti ={⊤}=∗ muHeld s γ crev ti ∗ ⌜crev = -1⌝ := by
  iintro #Hf H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha, Hfs⟩
  iunfold muInvAt at Ha
  iNamed Ha
  imod crevFrozen_agree γ _ crev HcM $$ Hf HcrevM with ⟨HcrevM, %Hc⟩
  imodintro
  iframe
  isplitl
  · iunfold muHeld; iframe Hl Hfs
    iunfold muInvAt; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
  ipureintro; exact Hc

theorem isTxnRead_frozen (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64)
    (crev : Int) :
    isTxnRead (GF := GF) mw s γ trace log rev crev (crevFrozen γ) ={⊤}=∗
      isTxnRead mw s γ trace log rev crev (crevFrozen γ) ∗ ⌜crev = -1⌝ := by
  iintro H
  iunfold isTxnRead at H
  iNamed H
  ihave #Htr' := Htr
  iunfold storeTxnReadIs at Htr'
  iNamedSuffix Htr' "T"
  ihave #HZT' : crevFrozen (GF := GF) (γ.withPhys p) $$ [HZT]
  · rw [crevFrozen_withPhys]; iexact HZT
  imod muHeld_frozen s (γ.withPhys p) crev ti $$ HZT' Hmu with ⟨Hmu, %Hc⟩
  imodintro
  isplitl
  · iunfold isTxnRead
    iexists p, trw, tr, ti, rt, ranges
    simp only [named]
    iframe
    iframe #
  ipureintro; exact Hc

/-- **The `mvcc.KV` `kv` over the store `s`** (persistent; unit N4, D14a): the store itself, or a
watchable store `ws` whose embedded `store` is `s` (whose `Read`, promoted, is `s`'s:
`KVView.lean`). -/
def kvOver (kv : GoInterface) (s : Loc) : IProp GF :=
  iprop(⌜kv = interface.mkOk (go.GoType.PointerType store.ty) #s⌝ ∨
    ∃ ws : Loc, ⌜kv = interface.mkOk (go.GoType.PointerType watchableStore.ty) #ws⌝ ∗
      ws.[watchableStore, go!"store"] ↦□ s)

instance kvOver_persistent (kv : GoInterface) (s : Loc) : Persistent (kvOver (GF := GF) kv s) := by
  unfold kvOver; infer_instance

/-- The store's `readView` (`kv_view.go`): its `kv` is a KV over the store `s` (`kvOver`: the
store itself, as `NewStore` makes it, or the watchable store `newWatchableStore` points it at;
unit N4, D14a: it was the store only). -/
def isReadView (rv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ kv : GoInterface, "#Hkv" ∷ rv.[readView, go!"kv"] ↦□ kv ∗ "#Hkvo" ∷ kvOver kv s ∗
    "#Hs" ∷ isStore s γ)

instance isReadView_persistent (rv s : Loc) (γ : StoreNames) :
    Persistent (isReadView (GF := GF) rv s γ) := by
  unfold isReadView; infer_instance

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

/-- The key-values of a `RangeResult` (`KVs`): fresh, one per answer of the index, in order,
each the state's key-value of the answer's key. -/
def rangeKvs (full : Bool) (kvs : GoSlice) (st : List EtcdKv)
    (answers : List (GoString × Rev × w64 × w64)) : IProp GF :=
  iprop(∃ ps : List Loc, kvs ↦* ps ∗ ⌜ps.length = answers.length⌝ ∗
    [∗list] pa ∈ ps.zip answers, ∃ kv : EtcdKv, ⌜findKey pa.2.1 st = some kv⌝ ∗ kvPtrIs full pa.1 kv)

/-- The revision a range read answers at: the option's, or the transaction's if the option's
is not positive. -/
def rangeRev (rev optRev : w64) : w64 := if sint.Z optRev ≤ 0 then rev else optRev

/-- **An error `fmt.Errorf` returned** (persistent), as Perennial's model of `fmt.Errorf` makes
it: `errors.New` of the format (`Perennial/TrustedCode/fmt.lean`: the arguments, `%w` included,
are ignored), an `*errors.errorString` whose `Error()` returns. Go's `fmt.Errorf` with `%w`
returns a `*fmt.wrapError` instead, which `errors.Is` sees through to the wrapped error: the
model does not (2026-10-12, the request path's unit 3b: `rangeKeys`' context error, and the txn
package's `executeTxn` wrapping it, reach the gRPC layer; `notes/STATUS.md`, "Unit 3b").
Not from the trust-boundary axiom `fmt.Errorf.wp_proof` (`Spec/fmt/Errorf.lean`, which gives
only that `Error()` returns): what the gRPC layer needs of the error (`applyErrIs`: a leaf
pointer error) is true of the model's `*errors.errorString` but not of Go's `*fmt.wrapError`,
whose `Unwrap` `errors.Is` follows, so an axiom stating it would be false of Go (2026-10-13, the
merge of `origin/lean`; `notes/decisions.md`, "`fmt.Errorf`'s `%w` errors: the model's body, not
the axiom"). -/
def errorfIs (err : GoInterface) : IProp GF :=
  iprop(∃ x : Loc,
    ⌜err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }})

omit package_sem in
instance errorfIs_persistent (err : GoInterface) : Persistent (errorfIs (GF := GF) err) := by
  unfold errorfIs; infer_instance

omit package_sem in
theorem errorfIs_ne_nil (err : GoInterface) : errorfIs (GF := GF) err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  iunfold errorfIs
  iintro ⟨%x, %h, -⟩
  ipureintro; subst h; intro h; cases h

/-- What `rangeKeys(ctx, key, end, rev, ro)` returns (`r`, `err`) of the committed log `log`
at the transaction's revision `rev`, for `[k, e)` (`endNil`: no end key):
* a future revision (`ro.Rev > rev`): `ErrFutureRev` and a count of `-1`;
* the context done (a full read only): no result and `fmt.Errorf`'s error (`errorfIs`);
* else the answer at `rangeRev rev ro.Rev`: the count alone (`CountOnly`), or the key-values
  of the index's answers (at most the limit), keys and revisions only (`FastKeysOnly`) or the
  state's key-values from the bucket, with the index's count. -/
def rangeOutcome (r : Loc) (err : GoInterface) (log : Log) (rev : w64) (endNil : Bool)
    (k e : GoString) (ro : RangeOptions) : IProp GF :=
  iprop(
    (⌜sint.Z rev < sint.Z ro.Rev'⌝ ∗
      (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
      r ↦ ({ KVs' := slice.nil, Rev' := rev, Count' := W64 (-1) } : RangeResult)) ∨
    (⌜sint.Z ro.Rev' ≤ sint.Z rev⌝ ∗ ⌜ro.CountOnly' = false ∧ ro.FastKeysOnly' = false⌝ ∗
      ⌜r = null⌝ ∗ errorfIs err) ∨
    (⌜sint.Z ro.Rev' ≤ sint.Z rev⌝ ∗ ⌜err = GoInterface.nil⌝ ∗
      if ro.CountOnly' then
        r ↦ ({
          KVs' := slice.nil, Rev' := rev,
          Count' := W64 (rangeAnswers log endNil k e (rangeRev rev ro.Rev')).length } : RangeResult)
      else ∃ kvs : GoSlice,
        r ↦ ({
          KVs' := kvs, Rev' := rev,
          Count' := W64 (rangeTotal log endNil k e (rangeRev rev ro.Rev') ro.Limit'
            ro.WithTotalCount') } : RangeResult) ∗
        rangeKvs (!ro.FastKeysOnly') kvs (stateAt log (sint.nat (rangeRev rev ro.Rev')))
          (rangeTaken log endNil k e (rangeRev rev ro.Rev') ro.Limit')))

/-- What `rangeKeys` returns at the compaction revision `c` (`compactMainRev`, as the
transaction reads it under `s.mu`): a read at a revision below `c` (`rangeRev rev ro.Rev < c`,
after the future-revision check) is `ErrCompacted` with the result `{KVs: nil, Count: -1, Rev:
0}`; otherwise `rangeOutcome`. At `c = -1` (no compaction) it is `rangeOutcome`
(`rangeOutcomeC_neg`). -/
def rangeOutcomeC (r : Loc) (err : GoInterface) (log : Log) (rev : w64) (c : Int) (endNil : Bool)
    (k e : GoString) (ro : RangeOptions) : IProp GF :=
  iprop(
    (⌜sint.Z ro.Rev' ≤ sint.Z rev ∧ sint.Z (rangeRev rev ro.Rev') < c⌝ ∗
      (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
      r ↦ ({ KVs' := slice.nil, Rev' := W64 0, Count' := W64 (-1) } : RangeResult)) ∨
    (⌜sint.Z ro.Rev' ≤ sint.Z rev → c ≤ sint.Z (rangeRev rev ro.Rev')⌝ ∗
      rangeOutcome r err log rev endNil k e ro))

/-- With no compaction, the outcome is `rangeOutcome` (the revision read at is not negative). -/
theorem rangeOutcomeC_neg (r : Loc) (err : GoInterface) (log : Log) (rev : w64) (endNil : Bool)
    (k e : GoString) (ro : RangeOptions) (hrev : 0 ≤ sint.Z rev) :
    rangeOutcomeC (GF := GF) r err log rev (-1) endNil k e ro ⊢ rangeOutcome r err log rev endNil k e ro := by
  iintro H
  iunfold rangeOutcomeC at H
  icases H with (⟨%Hc, -, -⟩ | ⟨-, H⟩)
  · exfalso
    unfold rangeRev at Hc
    split at Hc <;> omega
  · iexact H

/-- **A read the compaction did not reach** (M2, `notes/m2-plan.md`, S1): when the revision read at
is not below the transaction's compaction revision `crev`, the outcome is `rangeOutcome`. -/
theorem rangeOutcomeC_live (r : Loc) (err : GoInterface) (log : Log) (rev : w64) (crev : Int)
    (endNil : Bool) (k e : GoString) (ro : RangeOptions)
    (h : sint.Z ro.Rev' ≤ sint.Z rev → crev ≤ sint.Z (rangeRev rev ro.Rev')) :
    rangeOutcomeC (GF := GF) r err log rev crev endNil k e ro ⊢ rangeOutcome r err log rev endNil k e ro := by
  iintro H
  iunfold rangeOutcomeC at H
  icases H with (⟨%Hc, -, -⟩ | ⟨-, H⟩)
  · exfalso
    have := h Hc.1
    omega
  · iexact H

/-- **A latest read is never compacted** (M2, S1): a read at the transaction's revision
(`ro.Rev' ≤ 0`), whose compaction revision is at most it, has the outcome `rangeOutcome`. -/
theorem rangeOutcomeC_latest (r : Loc) (err : GoInterface) (log : Log) (rev : w64) (crev : Int)
    (endNil : Bool) (k e : GoString) (ro : RangeOptions) (hro : sint.Z ro.Rev' ≤ 0)
    (hc : crev ≤ sint.Z rev) :
    rangeOutcomeC (GF := GF) r err log rev crev endNil k e ro ⊢ rangeOutcome r err log rev endNil k e ro :=
  rangeOutcomeC_live r err log rev crev endNil k e ro (fun _ => by unfold rangeRev; simp [hro]; exact hc)

/-! ## The write transaction -/

/-- **The write transaction's lock token** at the puts `l`: the batch transaction's (`Locked l`),
or, after the lessor's delete from the `Lease` bucket (`ld`: `batchTxSpecG`'s last clause;
leases T3, 2026-10-25), a token only `Unlock` takes (`unlockAt`). -/
abbrev lockedIs (ld : Bool) (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W P : IProp GF)
    (Locked : Puts → IProp GF) (l : Puts) : IProp GF :=
  match ld with
  | false => Locked l
  | true => iprop(∃ U : IProp GF, U ∗ unlockAt bt View W P U l)

/-- Either token can be unlocked (`unlockAt`). -/
theorem lockedIs_unlock (ld : Bool) (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF)
    (P : IProp GF) (HF : val → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (MW : IProp GF) (l : Puts) :
    batchTxSpecG (GF := GF) bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW ∗
      lockedIs ld bt View W P Locked l ⊢ ∃ U : IProp GF, U ∗ unlockAt bt View W P U l := by
  iintro ⟨#Hbt, Hl⟩
  cases ld with
  | true => iexact Hl
  | false =>
    iexists (Locked l)
    iframe Hl
    iunfold batchTxSpecG at Hbt
    icases Hbt with ⟨-, -, #HU0, #HU, -⟩
    iunfold unlockAt
    isplitr
    · iintro !> %Φ !> ⟨Hl, %Hn, HW, HP⟩ HΦ
      subst Hn
      iapply HU0 $$ [$Hl $HW $HP] HΦ
    · iintro !> %m %Q %Φ !> ⟨Hl, Hv, Hw, HP⟩ HΦ
      iapply HU $$ %l %m %Q [$Hl $Hv $Hw $HP] HΦ

/-- The `*mvccpb.KeyValue`s of a write transaction's `changes`: the `i`-th holds what the
`i`-th pending change wrote (`changeKv`: the new key-value of a put, the key alone of a
delete). -/
def changesAre (ps : List Loc) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop([∗list] i ↦ p ∈ ps, ∃ kv : EtcdKv,
    ⌜changeKv (W64 ilog.length) (stateAfter ilog) pend i = some kv⌝ ∗ kvPtrIs true p kv)

/-- One more change: its key-value, at the pending revision after the changes so far, appended
to the `changes`. -/
theorem changesAre_snoc (ps : List Loc) (ilog : Log) (pend : List Change) (c : Change) (p : Loc)
    (kv : EtcdKv) (hps : ps.length = pend.length)
    (hkv : changeKv (W64 ilog.length) (stateAfter ilog) (pend ++ [c]) pend.length = some kv) :
    changesAre (GF := GF) ps ilog pend ∗ kvPtrIs true p kv ⊢
      changesAre (ps ++ [p]) ilog (pend ++ [c]) := by
  unfold changesAre
  refine (sep_mono (BigSepL.bigSepL_mono ?_) ?_).trans BigSepL.bigSepL_snoc.2
  · intro i p' hi
    rw [changeKv_append_lt _ _ _ _ (by have := (List.getElem?_eq_some_iff.1 hi).1; omega)]
  · rw [hps]
    iintro H
    iexists kv
    isplitl []
    · ipureintro; exact hkv
    iexact H

/-- The `storeTxnWrite` at `tw` of a write transaction of the store `s` at the committed log
`ilog`, with the pending changes `pend` (the next revision's, not yet visible to readers): its
fields (`beginRev` is `ilog`'s last revision, `changes` the key-values written), the batch
transaction locked with the pending puts, the writer's state (`writerL`, checked out of
`writerInv`, with the pending changes in the index writer's handle) and the batch lock's resource
(`writerRes`: the view's half, the compaction's part; its key deposited in `writerInv`), both
halves of the view's log ghost, the revision token the transaction was opened with, and the
transaction's tokens (with its slot of the index's lock, out of the readers' pool): `s.mu` held shared at the compaction revision `crev` the
transaction observed (one of `ilog`'s revisions, or `-1`), and the reader's tag `Z` (persistent,
given back at `End`). By default the frozen transaction (`crev = -1`, `Z = crevFrozen γ`: a store
never compacted, as the packages above mvcc state it; 2026-10-13, unit 6a). -/
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
    "#Hhook" ∷ hookOk γ Pw fw ∗
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw (hookFn γ) (storeRb γ) (kbMW γ.kb) ∗
    "#HbtB" ∷ storeBt γ bt ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "Hrt" ∷ storeRT γ ∗
    "Hlocked" ∷ lockedIs ld bt (bucketView γ) (storeW s γ) Pw Locked (pendPuts ilog pend) ∗
    "Hw" ∷ idxWriter γ.idx ilog pend ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap ilog) ∗
    "Hwv" ∷ ghostVar γ.wv 1 ilog ∗
    "Htko" ∷ ownToks γ.tko 1 ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hmu" ∷ muHeld s γ crev ti ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "Hcres" ∷ compactRes γ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "%Hcrev" ∷ ⌜-1 ≤ crev ∧ crev < ilog.length⌝ ∗
    "#HZ" ∷ □ Z)

/-- The write transaction of `storeTxnWriteIs` without its `changes` slice's contents and their
key-values (`chs ↦* ps`, `changesAre ps ilog pend`: the caller's, `storeTxnWrite.Changes`):
the slice is `chs`, of `ps.length = pend.length` pointers, and the index writer may be sealed
(`idxWriterB`: the watchable store seals the pending revision before it notifies). What
`storeTxnWrite.End` needs (it reads the slice's length only). -/
def storeTxnWriteCore (tw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (crev : Int)
    (Z : IProp GF := iprop(True)) (ld : Bool := false) : IProp GF :=
  iprop(∃ (ti : Loc) (bt : GoInterfaceOk) (Locked : Puts → IProp GF) (ntok : Nat)
    (Pw : IProp GF) (fw : val) (Dep : IProp GF),
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Htok" ∷ revToken γ ∗
    "Htw" ∷ tw ↦ ({
        storeTxnCommon' := {
          s' := s, tx' := GoInterface.ok bt, firstRev' := W64 0, rev' := W64 0, trace' := trace },
        tx' := GoInterface.ok bt, beginRev' := W64 ((ilog.length : Int) - 1),
        changes' := chs } : storeTxnWrite) ∗
    "Hcap" ∷ ownSliceCap Loc chs (DFrac.own 1) ∗
    "%Hps" ∷ ⌜ps.length = pend.length ∧ ps.length = sint.nat chs.len ∧ 0 ≤ sint.Z chs.len⌝ ∗
    "#Hs" ∷ isStore s γ ∗
    "#Hhook" ∷ hookOk γ Pw fw ∗
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw (hookFn γ) (storeRb γ) (kbMW γ.kb) ∗
    "#HbtB" ∷ storeBt γ bt ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "Hrt" ∷ storeRT γ ∗
    "Hlocked" ∷ lockedIs ld bt (bucketView γ) (storeW s γ) Pw Locked (pendPuts ilog pend) ∗
    "Hw" ∷ idxWriterB γ.idx ilog pend sealed ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap ilog) ∗
    "Hwv" ∷ ghostVar γ.wv 1 ilog ∗
    "Htko" ∷ ownToks γ.tko 1 ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hmu" ∷ muHeld s γ crev ti ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "Hcres" ∷ compactRes γ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "%Hcrev" ∷ ⌜-1 ≤ crev ∧ crev < ilog.length⌝ ∗
    "#HZ" ∷ □ Z)

/-- A write transaction's revision (`writeRev`) is not negative (kept). -/
theorem storeTxnWriteIs_writeRev (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (crev : Int) (Z : IProp GF) (ld : Bool) :
    storeTxnWriteIs (GF := GF) tw s γ trace ilog pend crev Z ld ⊢
      ⌜0 ≤ sint.Z (W64 ((writeRev ilog pend : Nat) : Int) : w64)⌝ := by
  iintro H
  iunfold storeTxnWriteIs at H
  iNamed H
  ipureintro
  have := writeRev_lt ilog pend Hne
  simp only [List.length_append, List.length_singleton] at this
  have hw : sint.Z (W64 ((writeRev ilog pend : Nat) : Int) : w64) = writeRev ilog pend := by
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  omega

/-- **A write transaction's changes are fewer than the receipts' bound** (D19c, 2026-10-18):
its index writer holds a receipt per change (`idxWriter_lt`), and the store's bound is
`2 ^ 48` (`isStore`). -/
theorem storeTxnWriteIs_small' (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (crev : Int) (Z : IProp GF) (ld : Bool) :
    storeTxnWriteIs (GF := GF) tw s γ trace ilog pend crev Z ld ⊢
      ⌜logCh ilog + pend.length < receiptBound GF ∧ receiptBound GF ≤ 2 ^ 48⌝ := by
  iintro H
  iunfold storeTxnWriteIs at H
  iNamed H
  iunfold isStore at Hs
  iNamedSuffix Hs "S"
  icases idxWriter_lt γ.idx ilog pend $$ Hw with ⟨%h, -⟩
  ipureintro; exact ⟨h, HrbS⟩

/-- The write transaction as its core, its `changes` and their key-values. -/
theorem storeTxnWriteIs_split (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (crev : Int) (Z : IProp GF := iprop(True)) (ld : Bool := false) :
    storeTxnWriteIs (GF := GF) tw s γ trace ilog pend crev Z ld ⊢
      ∃ (chs : GoSlice) (ps : List Loc), storeTxnWriteCore tw s γ trace ilog pend chs ps false crev Z ld ∗
        chs ↦* ps ∗ changesAre ps ilog pend := by
  iintro Htw
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
  iexists chs, ps
  iframe Hchs Hkvs
  iunfold storeTxnWriteCore
  iexists ti, bt, Locked, ntok, Pw, fw, Dep
  simp only [named, idxWriterB_false]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, ⟨Hps, Hlen.1, Hlen.2⟩, Hne, Htrnn, Hcrev⟩

theorem storeTxnWriteIs_join (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (crev : Int) (Z : IProp GF := iprop(True))
    (ld : Bool := false) :
    storeTxnWriteCore (GF := GF) tw s γ trace ilog pend chs ps false crev Z ld ∗ chs ↦* ps ∗
      changesAre ps ilog pend ⊢ storeTxnWriteIs tw s γ trace ilog pend crev Z ld := by
  iintro ⟨Hc, Hchs, Hkvs⟩
  iunfold storeTxnWriteCore at Hc
  iNamed Hc
  simp only [idxWriterB_false]
  iunfold storeTxnWriteIs
  iexists ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
  simp only [named]
  iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps.1, Hne, Htrnn, Hcrev⟩

/-- **The lessor's delete under the write transaction's lock** (leases T3, 2026-10-25): the
transaction's batch transaction `bt` deletes a key of the `Lease` bucket (`batchTxSpecG`'s last
clause, with the right to write the tracked buckets, `storeRb`), leaving the transaction with a
lock token only `Unlock` takes (`ld`: what `storeTxnWrite.End` takes; `lessor.Revoke` makes no
other call before it). -/
theorem storeTxnWriteIs_leaseDel (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (crev : Int) (Z : IProp GF) :
    storeTxnWriteIs (GF := GF) tw s γ trace ilog pend crev Z ⊢
      ∃ bt : GoInterfaceOk, storeBt γ bt ∗ ∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac)
          (r : GMap GoString backend.BktData) (Φ : val → IProp GF),
        globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b -∗ key ↦*{dq} k -∗
        storeRb γ r -∗
        ▷ (storeTxnWriteIs tw s γ trace ilog pend crev Z true -∗ key ↦*{dq} k -∗
          storeRb γ (rbDel r leaseName k) -∗ Φ #()) -∗
        WP (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key)) {{ Φ }} := by
  iintro Htw
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  iexists bt
  isplitr
  · iexact HbtB
  iintro %b %key %k %dq %r %Φ #HL Hkey Hrb HΦ
  ihave #Hbt0 : batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw (hookFn γ) (storeRb γ) (kbMW γ.kb) $$ []
  · iexact Hbt
  iunfold batchTxSpecG at Hbt0
  icases Hbt0 with ⟨-, -, -, -, -, -, -, -, #HDel⟩
  iapply HDel $$ %(pendPuts ilog pend) %b %key %k %dq %r [$HL $Hlocked $Hkey $Hrb]
  inext
  iintro ⟨Hlk, Hkey, Hrb⟩
  iapply HΦ $$ [-Hkey Hrb] Hkey Hrb
  iunfold storeTxnWriteIs
  iexists ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
  simp only [named]
  iframe
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩

/-- **Seal** the write transaction's pending revision (not empty): the log with the revision
committed is sealed (`idxSealed`: its history's lower bound and its well-formedness),
persistent. -/
theorem storeTxnWriteCore_seal (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (hne : pend ≠ []) (crev : Int)
    (Z : IProp GF := iprop(True)) (ld : Bool := false) :
    storeTxnWriteCore (GF := GF) tw s γ trace ilog pend chs ps false crev Z ld ==∗
      storeTxnWriteCore tw s γ trace ilog pend chs ps true crev Z ld ∗
        idxSealed γ.idx (ilog ++ [pend]) := by
  iintro Hc
  iunfold storeTxnWriteCore at Hc
  iNamed Hc
  simp only [idxWriterB_false]
  imod idxWriter_seal γ.idx ilog pend hne $$ Hw with ⟨Hw, #Hlb⟩
  imodintro
  iframe Hlb
  iunfold storeTxnWriteCore
  iexists ti, bt, Locked, ntok, Pw, fw, Dep
  simp only [named, idxWriterB_true]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩

/-- The write transaction's facts: the writer's log is well formed, and its committed log is
the store's view of `currentRev` (kept). -/
theorem storeTxnWriteCore_wf (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (b : Bool) (crev : Int) (Z : IProp GF := iprop(True))
    (ld : Bool := false) :
    storeTxnWriteCore (GF := GF) tw s γ trace ilog pend chs ps b crev Z ld ⊢
      storeTxnWriteCore tw s γ trace ilog pend chs ps b crev Z ld ∗
        ⌜IdxWf ilog pend ∧ ps.length = pend.length ∧ ps.length = sint.nat chs.len ∧
          0 ≤ sint.Z chs.len ∧ ilog ≠ []⌝ := by
  iintro Hc
  iunfold storeTxnWriteCore at Hc
  iNamed Hc
  ihave %Hwf := idxWriterB_wf γ.idx ilog pend b $$ Hw
  isplitl
  · iunfold storeTxnWriteCore
    iexists ti, bt, Locked, ntok, Pw, fw, Dep
    simp only [named]
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmu HrevMu Hti Hrt Hcres Hlrd
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩
  ipureintro; exact ⟨Hwf, Hps.1, Hps.2.1, Hps.2.2, Hne⟩

/-- The write transaction `store.Write` returns, as the caller sees it: the `metricsTxnWrite`
wrapper at `mw` (its counters `puts`, `deletes`, `putSize`) around the `storeTxnWrite`. -/
def isTxnWrite (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (crev : Int) (Z : IProp GF := iprop(True))
    (ld : Bool := false) : IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteIs tw s γ trace ilog pend crev Z ld ∗
    "Htrc" ∷ (∃ te : Bool, traceutil.ownTrace trace te))

open Iris.ProofMode in
/-- **A write transaction's changes are fewer than the receipts' bound** (D19c), keeping it. -/
theorem isTxnWrite_small (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) (ld : Bool) :
    isTxnWrite (GF := GF) mw s γ trace ilog pend puts deletes putSize crev Z ld ⊢
      ⌜logCh ilog + pend.length < receiptBound GF ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
        isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z ld := by
  refine (persistent_entails_left ?_).trans sep_comm.1
  iintro Ht
  iunfold isTxnWrite at Ht
  icases Ht with ⟨%tw, %ranges, Ht⟩
  iNamed Ht
  iapply storeTxnWriteIs_small' $$ Htw

/-- The write transaction at `mw` without its key-values (`storeTxnWriteCore`). -/
def isTxnWriteCore (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (sealed : Bool)
    (crev : Int) (Z : IProp GF := iprop(True)) (ld : Bool := false) : IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteCore tw s γ trace ilog pend chs ps sealed crev Z ld ∗
    "Htrc" ∷ (∃ te : Bool, traceutil.ownTrace trace te))

theorem isTxnWrite_split (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (crev : Int) (Z : IProp GF := iprop(True))
    (ld : Bool := false) :
    isTxnWrite (GF := GF) mw s γ trace ilog pend puts deletes putSize crev Z ld ⊢
      ∃ (chs : GoSlice) (ps : List Loc),
        isTxnWriteCore mw s γ trace ilog pend puts deletes putSize chs ps false crev Z ld ∗
        chs ↦* ps ∗ changesAre ps ilog pend := by
  iintro H
  iunfold isTxnWrite at H
  iNamed H
  icases storeTxnWriteIs_split tw s γ ilog pend crev Z ld $$ Htw with ⟨%chs, %ps, Hc, Hchs, Hkvs⟩
  iexists chs, ps
  iframe Hchs Hkvs
  iunfold isTxnWriteCore
  iexists tw, ranges
  iframe

theorem isTxnWrite_join (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (crev : Int)
    (Z : IProp GF := iprop(True)) (ld : Bool := false) :
    isTxnWriteCore (GF := GF) mw s γ trace ilog pend puts deletes putSize chs ps false crev Z ld ∗
      chs ↦* ps ∗ changesAre ps ilog pend ⊢
        isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z ld := by
  iintro ⟨H, Hchs, Hkvs⟩
  iunfold isTxnWriteCore at H
  iNamed H
  iunfold isTxnWrite
  iexists tw, ranges
  iframe Hmw Htrc
  iapply storeTxnWriteIs_join tw s γ ilog pend chs ps crev Z ld $$ [$Htw $Hchs $Hkvs]

/-- **The lessor's delete under the write transaction's lock**, through the `metricsTxnWrite`
wrapper (`storeTxnWriteIs_leaseDel`). -/
theorem isTxnWrite_leaseDel (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) :
    isTxnWrite (GF := GF) mw s γ trace ilog pend puts deletes putSize crev Z ⊢
      ∃ bt : GoInterfaceOk, storeBt γ bt ∗ ∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac)
          (r : GMap GoString backend.BktData) (Φ : val → IProp GF),
        globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ b -∗ key ↦*{dq} k -∗
        storeRb γ r -∗
        ▷ (isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z true -∗ key ↦*{dq} k -∗
          storeRb γ (rbDel r leaseName k) -∗ Φ #()) -∗
        WP (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key)) {{ Φ }} := by
  iintro H
  iunfold isTxnWrite at H
  iNamed H
  icases storeTxnWriteIs_leaseDel tw s γ ilog pend crev Z $$ Htw with ⟨%bt, #HbtB, Hd⟩
  iexists bt
  isplitr
  · iexact HbtB
  iintro %b %key %k %dq %r %Φ #HL Hkey Hrb HΦ
  iapply Hd $$ %b %key %k %dq %r %Φ HL Hkey Hrb
  inext
  iintro Htw Hkey Hrb
  iapply HΦ $$ [Hmw Htw Htrc] Hkey Hrb
  iunfold isTxnWrite
  iexists tw, ranges
  iframe

/-- **A write transaction's committed log is certified** (leases T3, L2b, 2026-10-25), keeping
it. -/
theorem isTxnWrite_cert (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) (ld : Bool) :
    isTxnWrite (GF := GF) mw s γ trace ilog pend puts deletes putSize crev Z ld ⊢
      isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z ld ∗ idxCert γ.idx ilog := by
  iintro H
  iunfold isTxnWrite at H
  iNamed H
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  iframe Hcert
  iunfold isTxnWrite
  iexists tw, ranges
  iframe Hmw Htrc
  iunfold storeTxnWriteIs
  iexists ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
  simp only [named]
  iframe
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩

theorem isTxnWriteCore_seal (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (hne : pend ≠ [])
    (crev : Int) (Z : IProp GF := iprop(True)) (ld : Bool := false) :
    isTxnWriteCore (GF := GF) mw s γ trace ilog pend puts deletes putSize chs ps false crev Z ld ==∗
      isTxnWriteCore mw s γ trace ilog pend puts deletes putSize chs ps true crev Z ld ∗
        idxSealed γ.idx (ilog ++ [pend]) := by
  iintro H
  iunfold isTxnWriteCore at H
  iNamed H
  imod storeTxnWriteCore_seal tw s γ ilog pend chs ps hne crev Z ld $$ Htw with ⟨Htw, #Hlb⟩
  imodintro
  iframe Hlb
  iunfold isTxnWriteCore
  iexists tw, ranges
  iframe

/-- **A frozen writer observed no compaction** (as `isTxnRead_frozen`). -/
theorem isTxnWrite_frozen (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) :
    isTxnWrite (GF := GF) mw s γ trace ilog pend puts deletes putSize crev (crevFrozen γ) ={⊤}=∗
      isTxnWrite mw s γ trace ilog pend puts deletes putSize crev (crevFrozen γ) ∗ ⌜crev = -1⌝ := by
  iintro H
  iunfold isTxnWrite at H
  iNamed H
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  imod muHeld_frozen s γ crev $$ HZ Hmu with ⟨Hmu, %Hc⟩
  imodintro
  isplitl
  · iunfold isTxnWrite
    iexists tw, ranges
    iframe Hmw Htrc
    iunfold storeTxnWriteIs
    iexists ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩
  ipureintro; exact Hc

/-- The log a write transaction commits at `End`: the pending revision appended, if it has a
change (else no revision is made). -/
def commitLog (ilog : Log) (pend : List Change) : Log :=
  if pend = [] then ilog else ilog ++ [pend]

open Iris.ProofMode in
open Iris.ProofMode in
/-- **Before a commit**: `s.revMu`'s fraction (`revQ γ 1`) and the caller's `logQPre` make the
half of the committed log's authority the index writer's commit needs. -/
theorem revQ_commit_pre (γ : StoreNames) (ilog : Log) (pend : List Change) (h : pend ≠ []) :
    idxLogAuth (GF := GF) γ.idx (revQ γ 1) ilog ∗ logQPre γ ilog pend ⊢
      idxLogAuth γ.idx (1 : Qp).half ilog := by
  have hq := (monoListAuthOwn_fractional (GF := GF) γ.idx.log ilog).fractional (1 : Qp).half.half
    (1 : Qp).half.half
  rw [Qp.half_add_half] at hq
  cases hw : γ.watchQ
  · rw [logQPre_plain γ ilog pend hw]
    simp only [revQ, hw, Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H, -⟩; iexact H
  · rw [logQPre_ne γ ilog pend h hw]
    simp only [revQ, logQ, idxLogAuth, hw, ↓reduceIte]
    iintro ⟨H1, H2⟩
    iapply hq.2; iframe H1 H2

open Iris.ProofMode in
/-- **After a commit**: the half back splits into `s.revMu`'s fraction and the caller's
`logQPost`. -/
theorem revQ_commit_post (γ : StoreNames) (ilog : Log) (pend : List Change) (h : pend ≠ []) :
    idxLogAuth (GF := GF) γ.idx (1 : Qp).half (ilog ++ [pend]) ⊢
      idxLogAuth γ.idx (revQ γ 1) (ilog ++ [pend]) ∗ logQPost γ ilog pend := by
  have hq := (monoListAuthOwn_fractional (GF := GF) γ.idx.log (ilog ++ [pend])).fractional
    (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at hq
  cases hw : γ.watchQ
  · rw [logQPost_plain γ ilog pend hw]
    simp only [revQ, hw, Bool.false_eq_true, ↓reduceIte]
    iintro H; iframe H
  · rw [logQPost_ne γ ilog pend h hw]
    simp only [revQ, logQ, idxLogAuth, hw, ↓reduceIte]
    iintro H
    iapply hq.1 $$ H

/-- A transaction behind a `metricsTxnWrite`: a read transaction, or a write transaction. -/
inductive TxnKind where
  | read (log : Log) (rev : w64)
  | write (ilog : Log) (pend : List Change) (puts deletes putSize : w64)

def isTxn (mw s : Loc) (γ : StoreNames) (trace : Loc) (kind : TxnKind) (crev : Int)
    (Z : IProp GF := iprop(True)) : IProp GF :=
  match kind with
  | .read log rev => isTxnRead mw s γ trace log rev crev Z
  | .write ilog pend puts deletes putSize =>
    isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z

/-- What `End` needs of a transaction (`metricsTxnWrite.End`): a read transaction; a write
transaction's core (its key-values released: `isTxnWrite_split`), sealed or not, its lock token
the batch transaction's or the one the lessor's delete left (`ld`, leases T3, 2026-10-25). -/
def isTxnEnd (mw s : Loc) (γ : StoreNames) (trace : Loc) (kind : TxnKind) (crev : Int)
    (Z : IProp GF := iprop(True)) : IProp GF :=
  match kind with
  | .read log rev => isTxnRead mw s γ trace log rev crev Z
  | .write ilog pend puts deletes putSize =>
    iprop(∃ (chs : GoSlice) (ps : List Loc) (sealed ld : Bool),
      isTxnWriteCore mw s γ trace ilog pend puts deletes putSize chs ps sealed crev Z ld)

/-- A transaction is ready to end (its key-values, if any, dropped). -/
theorem isTxn_toEnd (mw s : Loc) (γ : StoreNames) (kind : TxnKind) (crev : Int)
    (Z : IProp GF := iprop(True)) :
    isTxn (GF := GF) mw s γ trace kind crev Z ⊢ isTxnEnd mw s γ trace kind crev Z := by
  cases kind with
  | read log rev => exact .rfl
  | write ilog pend puts deletes putSize =>
    simp only [isTxn, isTxnEnd]
    iintro H
    icases isTxnWrite_split mw s γ ilog pend puts deletes putSize crev Z $$ H with ⟨%chs, %ps, Hc, -, -⟩
    iexists chs, ps, false, false
    iexact Hc

/-- A read transaction's trace, borrowed (its owner steps it while the transaction is live). -/
theorem isTxnRead_trace_acc (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64)
    (crev : Int) (Z : IProp GF := iprop(True)) :
    isTxnRead (GF := GF) mw s γ trace log rev crev Z ⊢
      (∃ te, traceutil.ownTrace trace te) ∗
        ((∃ te, traceutil.ownTrace trace te) -∗ isTxnRead mw s γ trace log rev crev Z) := by
  iintro H
  iunfold isTxnRead at H
  iNamed H
  iframe Htrc
  iintro Htrc
  iunfold isTxnRead
  iexists p, trw, tr, ti, rt, ranges
  iframe
  iframe #

/-- A write transaction's trace, borrowed. -/
theorem isTxnWrite_trace_acc (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int)
    (Z : IProp GF := iprop(True)) :
    isTxnWrite (GF := GF) mw s γ trace ilog pend puts deletes putSize crev Z ⊢
      (∃ te, traceutil.ownTrace trace te) ∗
        ((∃ te, traceutil.ownTrace trace te) -∗
          isTxnWrite mw s γ trace ilog pend puts deletes putSize crev Z) := by
  iintro H
  iunfold isTxnWrite at H
  iNamed H
  iframe Htrc
  iintro Htrc
  iunfold isTxnWrite
  iexists tw, ranges
  iframe

/-- **A transaction's trace, borrowed** (`store.Read`/`Write` took it: its owner steps it while
the transaction is live, and gives it back). -/
theorem isTxn_trace_acc (mw s : Loc) (γ : StoreNames) (trace : Loc) (kind : TxnKind)
    (crev : Int) (Z : IProp GF := iprop(True)) :
    isTxn (GF := GF) mw s γ trace kind crev Z ⊢
      (∃ te, traceutil.ownTrace trace te) ∗
        ((∃ te, traceutil.ownTrace trace te) -∗ isTxn mw s γ trace kind crev Z) := by
  cases kind with
  | read log rev => exact isTxnRead_trace_acc mw s γ trace log rev crev Z
  | write ilog pend puts deletes putSize =>
    exact isTxnWrite_trace_acc mw s γ trace ilog pend puts deletes putSize crev Z

/-- What `End` leaves of a transaction: nothing of a read one; of a write one, the
certificate of the committed log, the revision token back if no revision was made, and the
writer's fragment back (D22 receiver epochs, S5b: `txnEndPre`'s `hookIs`). -/
def txnEndPost (γ : StoreNames) : TxnKind → IProp GF
  | .read _ _ => iprop(True)
  | .write ilog pend _ _ _ =>
    iprop(idxCert γ.idx (commitLog ilog pend) ∗ (if pend = [] then revToken γ else iprop(True)) ∗
      logQPost γ ilog pend ∗ writerFrag γ)

/-- What `End` takes of a transaction: nothing of a read one; of a write one, the batch lock's
invariant `P` (the store's: `hookIs`), which `Unlock` takes back, and the outer quarter of the
committed log's authority for a commit (`logQPre`, unit W-K). -/
def txnEndPre (γ : StoreNames) : TxnKind → IProp GF
  | .read _ _ => iprop(True)
  | .write ilog pend _ _ _ => iprop(∃ (P : IProp GF) (f : val), hookIs γ P f ∗ P ∗
      certOkNext γ ilog pend ∗ logQPre γ ilog pend)

theorem txnEndPre_write (γ : StoreNames) (P : IProp GF) (f : val) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) :
    hookIs γ P f ∗ P ∗ certOkNext γ ilog pend ∗ logQPre γ ilog pend ⊢
      txnEndPre γ (.write ilog pend puts deletes putSize) := by
  iintro ⟨Hh, HP, #Hok, Hq⟩
  simp only [txnEndPre]
  iexists P, f
  iframe Hh HP Hok Hq

/-- `txnEndPre_write` for a store without watchers: no outer quarter (unit W-K). -/
theorem txnEndPre_write_plain (γ : StoreNames) (P : IProp GF) (f : val) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (h : γ.watchQ = false) :
    hookIs γ P f ∗ P ∗ certOkNext γ ilog pend ⊢
      txnEndPre γ (.write ilog pend puts deletes putSize) := by
  iintro ⟨Hh, HP, #Hok⟩
  iapply txnEndPre_write
  iframe Hh HP Hok
  rw [logQPre_plain γ ilog pend h]
  itrivial

/-- What `End` leaves of a write transaction of a store without watchers (unit W-K). -/
theorem txnEndPost_plain (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (h : γ.watchQ = false) :
    txnEndPost (GF := GF) γ (.write ilog pend puts deletes putSize) ⊢
      idxCert γ.idx (commitLog ilog pend) ∗ (if pend = [] then revToken γ else iprop(True)) ∗
        writerFrag γ := by
  simp only [txnEndPost]
  iintro ⟨Hc, Ht, -, Hf⟩
  iframe Hc Ht Hf

/-- The store's `writeView` (`kv_view.go`): its `kv` is the store `s`. -/
def isWriteView (wv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop("#Hkv" ∷ wv.[writeView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType store.ty) #s : GoInterface) ∗
    "#Hs" ∷ isStore s γ)

instance isWriteView_persistent (wv s : Loc) (γ : StoreNames) :
    Persistent (isWriteView (GF := GF) wv s γ) := by
  unfold isWriteView; infer_instance


/-! ## `restore` of a key bucket with data (D22 S-g) -/

/-- **The revisions a store can be restored with** after `NewStore`'s two (D22 S-g, 2026-10-19):
the log `[[], []] ++ R` (revision 0 and the store's first `currentRev`, both empty) whose further
revisions each have a change (an empty revision writes nothing to the `Key` bucket, so `restore`
could not see it: the restored `currentRev` is the last revision with an entry, the log's last),
well formed and bounded as the index writer's log (`IdxWf`), and with no put attached to a lease
(`restore` attaches the leases of the keys it finds through the lessor, `s.le.Attach`: not
modelled, and the server's workload grants none). -/
def restoreLogOk (R : Log) : Prop :=
  (∀ cs ∈ R, cs ≠ []) ∧ IdxWf ([[], []] ++ R) [] ∧
    ∀ cs ∈ R, ∀ c ∈ cs, ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0

/-- **The view `store.restore` reads** of the restored log `[[], []] ++ R`: the empty bucket
(`NewStore`'s), or the log's bucket over a clean read buffer (the restore plan's R5a, R5c). -/
def restoreViewOut (γ : StoreNames) (q : Qp) (R : Log) : IProp GF :=
  if R = [] then bucketView γ q ∅ else bucketViewC γ q (bucketMap ([[], []] ++ R))

/-- `restoreViewOut` with, for a bucket with data, the backend's clean-view `ReadTx`. -/
def restoreView (b : GoInterface) (γ : StoreNames) (RT : IProp GF) (q : Qp) (R : Log) : IProp GF :=
  iprop(restoreViewOut γ q R ∗
    (if R = [] then iprop(True) else keyCleanRead b (bucketViewC γ) RT (kbNoCmp γ.kb γ.bucket)))

/-- Two parts summing to one make the whole points-to. -/
theorem typedPointsto_parts {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (q1 q2 : Qp)
    (h : q1 + q2 = 1) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢ (l ↦{DFrac.own q1} v ∗ l ↦{DFrac.own q2} v) := by
  have h' : (DFrac.own 1 : DFrac) = DFrac.own q1 • DFrac.own q2 := by rw [DFrac.op_own, h]
  rw [h']
  exact (typedPointsto_dfractional (GF := GF) l v).dfractional _ _

/-- **`store.restore`'s lock of `s.revMu`** (the restore plan's R5e), as its caller gives it: from
`RevP`, `Lock` returns the lock's part `q` of `currentRev` (at some value: `restore`'s own part
says which), with `RevK` (`NewStore`: private memory; `store.Restore`: the lock in restoring mode,
whose parts of the counters are at any values). -/
def revLockW (s : Loc) (q : Qp) (RevP RevK : IProp GF) : IProp GF :=
  iprop(∀ Ψ : val → IProp GF, RevP -∗
    ▷ (∀ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own q} v : IProp GF) -∗ RevK -∗ Ψ #()) -∗
    WP (App (Val (s.[store, go!"revMu"] @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Lock"))
      (Val #())) {{ Ψ }})

/-- **`store.restore`'s unlock of `s.revMu`**: with the lock's part `q` of `currentRev` at the
restored log `L'`'s last revision, `RevK` and `V` (`restore`'s share of the bucket's view, idle
after its read transaction's `RLock`: `store.Restore` puts it in `s.revMu`'s body), `Unlock` gives
`RevQ`. -/
def revUnlockW (s : Loc) (q : Qp) (L' : Log) (RevK V RevQ : IProp GF) : IProp GF :=
  iprop(∀ Ψ : val → IProp GF,
    (s.[store, go!"currentRev"] ↦{DFrac.own q} (W64 ((L'.length : Int) - 1) : w64) : IProp GF) -∗
    RevK -∗ V -∗
    ▷ (RevQ -∗ Ψ #()) -∗
    WP (App (Val (s.[store, go!"revMu"] @!! go.GoType.PointerType sync.RWMutex.ty @!! go!"Unlock"))
      (Val #())) {{ Ψ }})

/-- `NewStore`'s log: no revision after its two. -/
theorem restoreLogOk_nil : restoreLogOk [] := by
  refine ⟨by simp, ⟨⟨fun _ => rfl, ?_⟩, by decide, by decide, by simp⟩, by simp⟩
  intro r cs i k hr hi
  have hcs : cs = [] := by
    rcases r with _ | _ | _ | r <;> simp_all
  subst hcs
  simp at hi

/-- Revisions each with a change have at least as many changes as revisions. -/
theorem length_le_logCh : ∀ (R : Log), (∀ cs ∈ R, cs ≠ []) → R.length ≤ logCh R
  | [], _ => by simp
  | cs :: R, h => by
    have h1 : 0 < cs.length := List.length_pos_iff.2 (h cs (by simp))
    have h2 := length_le_logCh R (fun c hc => h c (by simp [hc]))
    simp only [logCh, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    omega

/-- **A restored log has a revision per change past its first two** (what the sole writer's
`soleLog` asks: `txn.soleLog ([[], []] ++ R)`, D22 S-j). -/
theorem restoreLogOk_len {R : Log} (h : restoreLogOk R) :
    2 ≤ ([[], []] ++ R).length ∧ ([[], []] ++ R).length ≤ logCh ([[], []] ++ R) + 2 := by
  have := length_le_logCh R h.1
  have hc : logCh ([[], []] ++ R) = logCh R := by simp [logCh]
  simp only [List.length_append, hc]
  simp only [List.length_cons, List.length_nil]
  omega

end reprs

section hookLc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- Two views of the hook agree, the invariants now (a later credit spent): the same function,
each invariant gives the other. -/
theorem hookOk_agree_lc (E : CoPset) (γ : StoreNames) (P P' : IProp GF) (f f' : val) :
    £ 1 ∗ hookOk γ P f ∗ hookOk γ P' f' ⊢
      |={E}=> ⌜f = f'⌝ ∗ □ (P -∗ P') ∗ □ (P' -∗ P) := by
  iintro ⟨Hlc, #H1, #H2⟩
  ihave ⟨%Hf, Heq⟩ := hookOk_agree γ P P' f f' $$ [H1 H2]
  · iframe H1 H2
  imod lc_fupd_elim_later $$ Hlc Heq with #Heq
  ihave #Hiff := internalEq_iff P P' $$ Heq
  imodintro
  isplitl []
  · ipureintro; exact Hf
  isplitl []
  · iintro !> HP
    icases Hiff with ⟨#H, -⟩
    iapply H
    iexact HP
  · iintro !> HP
    icases Hiff with ⟨-, #H⟩
    iapply H
    iexact HP

/-- `hookOk_agree_lc` of two views of the store's hook (`hookIs`, each with a writer's fragment). -/
theorem hookIs_agree_lc (E : CoPset) (γ : StoreNames) (P P' : IProp GF) (f f' : val) :
    £ 1 ∗ hookIs γ P f ∗ hookIs γ P' f' ⊢
      |={E}=> ⌜f = f'⌝ ∗ □ (P -∗ P') ∗ □ (P' -∗ P) := by
  iintro ⟨Hlc, H1, H2⟩
  icases (hookIs_split γ P f).1 $$ H1 with ⟨#H1, -⟩
  icases (hookIs_split γ P' f').1 $$ H2 with ⟨#H2, -⟩
  iapply hookOk_agree_lc E γ P P' f f' $$ [$Hlc $H1 $H2]

/-- **The caller's hook against the store's recorded invariant** (`isStore`'s `hookP`; unit N4,
D14b: the store records no hook), one later credit. -/
theorem hookP_agree_lc (E : CoPset) (γ : StoreNames) (P P' : IProp GF) (f : val) :
    £ 1 ∗ hookOk γ P f ∗ hookP γ P' ⊢ |={E}=> □ (P -∗ P') ∗ □ (P' -∗ P) := by
  iintro ⟨Hlc, #H1, #H2⟩
  iunfold hookOk at H1
  icases H1 with ⟨#HP1, -⟩
  iunfold hookP at HP1 H2
  ihave Heq := saved_prop_agree γ.hook DFrac.discard DFrac.discard P P' $$ HP1 H2
  imod lc_fupd_elim_later $$ Hlc Heq with #Heq
  ihave #Hiff := internalEq_iff P P' $$ Heq
  imodintro
  isplitl []
  · iintro !> HP
    icases Hiff with ⟨#H, -⟩
    iapply H
    iexact HP
  · iintro !> HP
    icases Hiff with ⟨-, #H⟩
    iapply H
    iexact HP

/-- The batch lock's resource and the registration (done or pending) give the writer's resource,
the store registered (S6). -/
theorem writerReg_get (s : Loc) (γ : StoreNames) :
    storeW (GF := GF) s γ ∗ writerReg s γ ==∗ writerRes s γ ∗ storeRegd s γ := by
  iintro ⟨HW, Hrg⟩
  iunfold writerReg at Hrg
  icases Hrg with (#Hreg | ⟨Hrr, HWr⟩)
  · ihave HWr := storeW_get s γ $$ [$Hreg $HW]
    imodintro; iframe HWr Hreg
  · iapply storeW_pending s γ $$ [$HW $Hrr $HWr]

/-- **A writer checks the writer's state out** (one later credit), with the batch lock's resource
(`storeW`, from its `LockInsideApply`) and its part of `s.mu`'s deposit ghost, at its pin (S5b: the
state is at the current names, the pin's): the state is in (another writer's deposit would be a
second key); the store is registered in its backend (S6: if the registration is pending, after a
restore, it is made now: `storeW_pending`); the writer gets the batch lock's resource but its key,
which it deposits with its part of the deposit ghost. -/
theorem writerInv_checkout (s : Loc) (γ : StoreNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInv (GF := GF) s γ -∗ curAt γ dq o -∗ storeW s γ -∗ wDep γ ={⊤}=∗
      writerL s γ ∗ storeRegd s γ ∗
      (∃ L : Log, ghostVar γ.wv (1 : Qp).half L ∗ bucketView γ (1 : Qp).half (bucketMap L) ∗
        idxCert γ.idx L ∗ ⌜L ≠ []⌝ ∗ compactRes γ) ∗ curAt γ dq o := by
  iintro Hlc #Hi Hpin HW Hd
  iunfold writerInv at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨Hwr1, -⟩)
  rotate_left 1
  · iunfold wDep at Hd
    ihave %Hv := ghostVar_valid_2 γ.wr () 1 () _ $$ Hwr1 Hd
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨HL, Hrg⟩ | ⟨Hk', -, #Hreg'⟩)
  · imod writerReg_get s γ $$ [$HW $Hrg] with ⟨HWr, #Hreg⟩
    iunfold writerRes at HWr
    icases HWr with ⟨%L, Hwk, Hwv, Hbv, #Hcert, %Hne, Hcres⟩
    imod Hclose $$ [Hc Hwk Hd] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; iright; iframe Hwk Hd Hreg
    imodintro
    iframe HL Hreg Hpin
    iexists L
    iframe Hwv Hbv Hcert Hcres
    ipureintro; exact Hne
  · ihave HWr := storeW_get s γ $$ [$Hreg' $HW]
    iunfold writerRes at HWr
    icases HWr with ⟨%L, Hk, -⟩
    iunfold writerKey at Hk Hk'
    ihave %Hv := ghostVar_valid_2 γ.wk () 1 () 1 $$ Hk Hk'
    exact absurd Hv.1 (Qp_one_add_not_le 1)

/-- **A writer checks the writer's state back in** (one later credit), at its pin, getting the
batch lock's key and its part of `s.mu`'s deposit ghost back: the state is out (a second state's
half of the view's log ghost, with the writer's and the batch lock's, would be three halves); the
store stays registered (S6). -/
theorem writerInv_checkin (s : Loc) (γ : StoreNames) (L : Log) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ writerInv (GF := GF) s γ -∗ curAt γ dq o -∗ writerL s γ -∗
      ghostVar γ.wv (1 : Qp).half L ={⊤}=∗
      writerKey γ ∗ wDep γ ∗ ghostVar γ.wv (1 : Qp).half L ∗ curAt γ dq o := by
  iintro Hlc #Hi Hpin HL Hv
  iunfold writerInv at Hi
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hi with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨-, %h, Hh1⟩)
  rotate_left 1
  · iunfold writerL at HL
    icases HL with ⟨%l1, %n1, HL⟩
    iNamed HL
    iunfold idxWriter at Hw
    icases Hw with ⟨Hh2, -⟩
    ihave %Hv := monoListAuthOwn_agree γ.idx.hist 1 (1 : Qp).half _ _ $$ Hh2 Hh1
    exact absurd Hv.1 (Qp_one_add_not_le _)
  ihave %Hvv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hvv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨HL', -⟩ | ⟨Hk, Hd, #Hreg⟩)
  · iunfold writerL at HL HL'
    icases HL with ⟨%l1, %n1, HL⟩
    icases HL' with ⟨%l2, %n2, HL'⟩
    iNamedSuffix HL "1"
    iNamedSuffix HL' "2"
    icases ghostVar_join_halves γ.wv l1 l2 $$ [Hwv1 Hwv2] with ⟨Hwv12, -⟩
    · iframe Hwv1 Hwv2
    ihave %Hv3 := ghostVar_valid_2 γ.wv l1 1 L (1 : Qp).half $$ Hwv12 Hv
    exact absurd Hv3.1 (Qp_one_add_not_le _)
  · imod Hclose $$ [Hc HL] with -
    · inext; iunfold writerInvBody; ileft; iexists γ.phys, o'; rw [StoreNames.withPhys_self]
      iframe Hc; ileft; iframe HL
      iunfold writerReg; ileft; iexact Hreg
    imodintro; iframe Hk Hd Hv Hpin

/-- **A transaction checks a slot out of the readers' pool** (one later credit), with an idle
reader's ticket and its deposit (it holds `s.mu` shared), at a part of the current objects and
names (its pin, S5b): the slot, and a checked-out ticket. -/
theorem readerPool_checkout (γ : StoreNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ ownToks γ.tk 1 -∗ wDep γ ={⊤}=∗
      idxSlot γ o ∗ ownToks γ.tko 1 ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin Ht Hd
  iunfold readerPool at Hp
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hp with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%p, %o', Hc, HP⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  icombine Ha Ht gives %Hle
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tk k' $$ Ha Ht with Ha
  imod ownTokAuth_S γ.tko _ $$ Hao with ⟨Hao, Hto⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H1, Hs⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws Hd] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k', j + 1, w, r
    iframe Ha Hao Haw Har Hs Hws
    isplitl [Hds Hd]
    · rw [List.replicate_succ]; iapply BigSepL.bigSepL_cons.2; iframe Hd Hds
    ipureintro; omega
  imodintro
  iframe H1 Hto Hpin

/-- `readerPool_checkout` at a pin of some physical names `p` (a reader at the logical names
`γ`; S5b). -/
theorem readerPool_checkout_p (γ : StoreNames) (p : PhysNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt (γ.withPhys p) dq o -∗ ownToks γ.tk 1 -∗ wDep γ ={⊤}=∗
      idxSlot (γ.withPhys p) o ∗ ownToks γ.tko 1 ∗ curAt (γ.withPhys p) dq o :=
  readerPool_checkout (γ.withPhys p) dq o

/-- **A transaction checks its slot back in** (one later credit), with its checked-out ticket, at
its pin: an idle reader's ticket and its deposit back. -/
theorem readerPool_checkin (γ : StoreNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ idxSlot γ o -∗ ownToks γ.tko 1 ={⊤}=∗
      ownToks γ.tk 1 ∗ wDep γ ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin H1 Hto
  iunfold readerPool at Hp
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hp with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%p, %o', Hc, HP⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  icombine Hao Hto gives %Hle
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tko j' $$ Hao Hto with Hao
  imod ownTokAuth_S γ.tk k $$ Ha with ⟨Ha, Ht⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hds with ⟨Hd, Hds⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws H1] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k + 1, j', w, r
    iframe Ha Hao Haw Har Hds Hws
    isplitl [Hs H1]
    · rw [List.replicate_succ]; iapply BigSepL.bigSepL_cons.2; iframe H1 Hs
    ipureintro; omega
  imodintro
  iframe Ht Hd Hpin

/-- **The watchable store's `syncWatchers` checks a slot out** (D22 receiver epochs, S5a; one later
credit), with an idle reader's ticket and the watchable store's deposit (it holds the watchable
store's lock exclusively), at its pin: the slot, and a ticket checked out under that lock. -/
theorem readerPool_checkout_ws (γ : StoreNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ ownToks γ.tk 1 -∗ wsDep γ ={⊤}=∗
      idxSlot γ o ∗ ownToks γ.tkw 1 ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin Ht Hd
  iunfold readerPool at Hp
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hp with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%p, %o', Hc, HP⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  icombine Ha Ht gives %Hle
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tk k' $$ Ha Ht with Ha
  imod ownTokAuth_S γ.tkw _ $$ Haw with ⟨Haw, Htw⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H1, Hs⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws Hd] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k', j, w + 1, r
    iframe Ha Hao Haw Har Hs Hds
    isplitl [Hws Hd]
    · rw [List.replicate_succ]; iapply BigSepL.bigSepL_cons.2; iframe Hd Hws
    ipureintro; omega
  imodintro
  iframe H1 Htw Hpin

/-- **`syncWatchers` checks its slot back in** (S5a; one later credit), with its ticket, at its
pin: an idle reader's ticket and the watchable store's deposit back. -/
theorem readerPool_checkin_ws (γ : StoreNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ idxSlot γ o -∗ ownToks γ.tkw 1 ={⊤}=∗
      ownToks γ.tk 1 ∗ wsDep γ ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin H1 Htw
  iunfold readerPool at Hp
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hp with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%p, %o', Hc, HP⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  icombine Haw Htw gives %Hle
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tkw w' $$ Haw Htw with Haw
  imod ownTokAuth_S γ.tk k $$ Ha with ⟨Ha, Ht⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hws with ⟨Hd, Hws⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws H1] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k + 1, j, w', r
    iframe Ha Hao Haw Har Hds Hws
    isplitl [Hs H1]
    · rw [List.replicate_succ]; iapply BigSepL.bigSepL_cons.2; iframe H1 Hs
    ipureintro; omega
  imodintro
  iframe Ht Hd Hpin

/-- `readerPool_checkout_ws` at a pin of some physical names `p` (S5b). -/
theorem readerPool_checkout_ws_p (γ : StoreNames) (p : PhysNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt (γ.withPhys p) dq o -∗ ownToks γ.tk 1 -∗ wsDep γ ={⊤}=∗
      idxSlot (γ.withPhys p) o ∗ ownToks γ.tkw 1 ∗ curAt (γ.withPhys p) dq o :=
  readerPool_checkout_ws (γ.withPhys p) dq o

/-- `readerPool_checkin_ws` at a pin of some physical names `p` (S5b). -/
theorem readerPool_checkin_ws_p (γ : StoreNames) (p : PhysNames) (dq : DFrac) (o : StoreObjs) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt (γ.withPhys p) dq o -∗ idxSlot (γ.withPhys p) o -∗
      ownToks γ.tkw 1 ={⊤}=∗ ownToks γ.tk 1 ∗ wsDep γ ∗ curAt (γ.withPhys p) dq o :=
  readerPool_checkin_ws (γ.withPhys p) dq o

/-- **A reader retires its ticket for a backend token of its own** (D22 receiver epochs, S5a; one
later credit), at a pin: a slot out of the pool for good, its index slot dropped (the apply
thread's token, for its writes under the batch lock, which borrow one: `apply.kvOwn`; the storage
version monitor's). A restore takes the retired tokens back from their holders. -/
theorem readerPool_retire (γ : StoreNames) (dq : DFrac) (o : StoreObjs) (n : Nat) :
    ⊢ £ 1 -∗ readerPool (GF := GF) γ -∗ curAt γ dq o -∗ ownToks γ.tk 1 -∗ retiredAt γ n ={⊤}=∗
      storeRT γ ∗ retiredAt γ (n + 1) ∗ curAt γ dq o := by
  iintro Hlc #Hp Hpin Ht Hret
  iunfold readerPool at Hp
  imod inv_acc (E := ⊤) (N := poolN) (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))
    (by exact CoPset.subseteq_top) $$ Hp with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := iprop(∃ (p : PhysNames) (o : StoreObjs),
      curAt (GF := GF) (γ.withPhys p) (DFrac.own (1 : Qp).half.half.half) o ∗
        poolBody (γ.withPhys p) o))) $$ Hlc HP with HP
  icases HP with ⟨%p, %o', Hc, HP⟩
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  iunfold poolBody at HP
  icases HP with ⟨%k, %j, %w, %r, Ha, Hao, Haw, Har, Hs, Hds, Hws, %Hk⟩
  icombine Ha Ht gives %Hle
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  imod ownTokAuth_delete_S γ.tk k' $$ Ha Ht with Ha
  iunfold retiredAt at Hret
  ihave %Hrn := ghostVar_agree (GF := GF) γ.tkr r _ n _ $$ Har Hret
  subst Hrn
  imod ghostVar_update_halves (GF := GF) (r + 1) γ.tkr r r $$ Har Hret with ⟨Har, Htr⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨H1, Hs⟩
  imod Hclose $$ [Hc Ha Hao Haw Har Hs Hds Hws] with -
  · inext
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    iunfold poolBody
    iexists k', j, w, r + 1
    iframe Ha Hao Haw Har Hs Hds Hws
    ipureintro; omega
  iunfold idxSlot at H1
  icases H1 with ⟨-, Hrt⟩
  imodintro
  iframe Hrt Hpin
  iunfold retiredAt
  iexact Htr

/-- **An idle reader retires its ticket** (S5a; one later credit; `readerPool_retire`), at a pin: a
backend token of its own, its slots of the store's locks dropped. -/
theorem storeReader_retire (s : Loc) (γ : StoreNames) (dq : DFrac) (o : StoreObjs) (n : Nat) :
    ⊢ £ 1 -∗ isStore (GF := GF) s γ -∗ curAt γ dq o -∗ storeReader s γ -∗ retiredAt γ n ={⊤}=∗
      storeRT γ ∗ retiredAt γ (n + 1) ∗ curAt γ dq o := by
  iintro Hlc #Hs Hpin Hr Hret
  iunfold isStore at Hs
  iNamed Hs
  iunfold storeReader at Hr
  iNamed Hr
  iapply readerPool_retire γ dq o n $$ Hlc Hpool Hpin Htk Hret

/-- A stop channel (persistent): a broadcast channel of `True`, maybe closed (the store's
`stopc`; the watchable store's). Moved from `InvWatchStore.lean` (2026-10-13). -/
def isStopChan (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan c γc iprop(True) Broadcast.Unknown)

instance isStopChan_persistent (c : Loc) : Persistent (isStopChan (GF := GF) c) := by
  unfold isStopChan; infer_instance

/-- The right to close the stop channel `c` (once): its broadcast, still pending. Moved from
`InvWatchSync.lean` (2026-10-13). -/
def stopCloser (c : Loc) : IProp GF :=
  iprop(∃ γc : ChanNames, ownBroadcastChan c γc iprop(True) Broadcast.Pending)

/-- **The store's fields for good, for its compaction** (persistent; D22 receiver epochs, S3,
2026-10-22: until then `NewStore` returned the stop channel's `↦□` and `isStore` the others'):
the four fields `store.Restore` writes, read-only, at the pinned objects, and the stop channel
(the compaction job's loop selects on it). Only the compaction right is made with it
(`compactRight_of_closer`, which gives up the right to close the store, so a store with it is
never restored: `store.Restore` takes the right to close). -/
def storeStop (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ o : StoreObjs, curAt γ DFrac.discard o ∗ storeFields s o DFrac.discard ∗
    isStopChan o.sstop ∗ dghostVar γ.rst DFrac.discard false ∗ □ physOk s γ o)

instance storeStop_persistent (s : Loc) (γ : StoreNames) : Persistent (storeStop (GF := GF) s γ) := by
  unfold storeStop storeFields; simp only [named]; infer_instance

/-- The compaction's objects (D22 receiver epochs, S5b: the current ones for good, the closer's
part of them discarded): their fields read-only, the stop channel, the restoring flag down for
good, and what they are (`physOk`). -/
theorem storeStop_open (s : Loc) (γ : StoreNames) :
    storeStop (GF := GF) s γ ⊢ ∃ (b : GoInterface) (ti : Loc) (ssched : GoInterface) (sstop : Loc),
      (s.[store, go!"b"] ↦□ b : IProp GF) ∗
      (s.[store, go!"kvindex"] ↦□
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) : IProp GF) ∗
      (s.[store, go!"fifoSched"] ↦□ ssched : IProp GF) ∗
      (s.[store, go!"stopc"] ↦□ sstop : IProp GF) ∗ isStopChan sstop ∗
      dghostVar γ.rst DFrac.discard false ∗ □ physOk s γ ⟨b, ti, ssched, sstop⟩ ∗
      curAt γ DFrac.discard ⟨b, ti, ssched, sstop⟩ := by
  unfold storeStop
  iintro ⟨%o, #Hc, #H, #Hsc, #Hr, #Hph⟩
  obtain ⟨b, ti, ssched, sstop⟩ := o
  iexists b, ti, ssched, sstop
  iunfold storeFields at H
  iNamed H
  iframe #

/-- **The fields' shares gathered** (`store.Restore`, the restore plan's R5f): `s.mu`'s half, the
caller's quarter and the closer's quarter, at the closer's objects and names, make the whole. -/
theorem fieldShare_gather (s : Loc) (γ : StoreNames) (o : StoreObjs) :
    fieldShare (GF := GF) s γ (1 : Qp).half ∗ fieldShare s γ (1 : Qp).half.half ∗
      fieldShareAt s γ (1 : Qp).half.half o ⊢ fieldShareAt s γ 1 o := by
  iintro ⟨H1, H2, H3⟩
  ihave H12 := ((fieldShare_fractional (GF := GF) s γ).fractional (1 : Qp).half (1 : Qp).half.half).2
    $$ [H1 H2]
  · iframe H1 H2
  iunfold fieldShare at H12
  icases H12 with ⟨%p, %o', H12⟩
  ihave %Hv := curAt_pin γ p (DFrac.own (1 : Qp).half.half.half)
    (DFrac.own ((1 : Qp).half + (1 : Qp).half.half).half) o o' $$ [H3 H12]
  · iunfold fieldShareAt at H3 H12
    iNamedSuffix H3 "3"
    iNamedSuffix H12 "12"
    iframe Hcur3 Hcur12
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self] at *
  have h : ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half = 1 := by
    rw [show (1 : Qp).half + (1 : Qp).half.half + (1 : Qp).half.half =
      (1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half) from by
        apply Subtype.ext; simp only [Qp.val_add]; grind]
    rw [Qp.half_add_half, Qp.half_add_half]
  have hs := (fieldShareAt_split (GF := GF) s γ ((1 : Qp).half + (1 : Qp).half.half)
    (1 : Qp).half.half o').2
  rw [h] at hs
  iapply hs
  iframe H12 H3

/-- **The right to close the store** `s` (`store.Close`: `close(s.stopc)`, once, and
`s.fifoSched.Stop()`; `NewStore` returns it): the stop channel's close (`stopCloser`), the
scheduler's stop token (`schedStopTok`: no untracked `Schedule` after `Stop`, which panics there)
and the compaction jobs' queue at `-1` (`compactQueue`, which holds the scheduler's tracked queue:
no tracked `Schedule` after `Stop` either; `Scheduler.Stop`'s spec takes both), with a quarter of
the fields at the current objects and names, `γ`'s (D22 receiver epochs, S5b: the closer's names
are the current ones). D19m (C), 2026-10-18: until then only the channel's close, with the stop
token given up by `NewStore`, so `Close`'s contract let a holder of `isStore` compact after
`Close`. A caller that will not close the store gives the token up for the compaction right
(`compactRight_of_closer`), or drops this. -/
def storeCloser (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ o : StoreObjs, fieldShareAt s γ (1 : Qp).half.half o ∗ isStopChan o.sstop ∗
    stopCloser o.sstop ∗ schedule.schedStopTok γ.sch ∗ compactQueue γ (-1))

/-- **The compaction right, from the right to close the store** (D22 receiver epochs, S3): the
scheduler's stop token given up for good (`schedLive`), the closer's share of the fields
discarded (`storeStop`, for the compaction's jobs, which run without the store's locks; S5b: with
its part of the current objects and names, so the store is never restored), with the compaction
right's half of the revision's authority (`NewStore`'s). The store is then never closed, nor
restored. -/
theorem compactRight_of_closer (s : Loc) (γ : StoreNames) :
    storeCloser (GF := GF) s γ ∗ crevUB γ.idx (1 : Qp).half (-1) ==∗
      compactRight γ (-1) ∗ storeStop s γ := by
  unfold storeCloser fieldShareAt
  iintro ⟨⟨%o, ⟨Hc, Hf, Hr, #Hph⟩, #Hsc, -, Htok, Hq⟩, Hcu⟩
  imod dghostVar_persist γ.rst _ false $$ Hr with #Hr
  iunfold curAt at Hc
  imod dghostVar_persist γ.cur _ _ $$ Hc with #Hc
  iunfold schedule.schedStopTok at Htok
  icases Htok with ⟨%n, #Hn, Hd⟩
  imod dghostVar_persist n 1 () $$ Hd with #Hd
  iunfold storeFields at Hf
  icases Hf with ⟨Hfb, Hfidx, Hfsch, Hfstop⟩
  ipersist Hfb
  ipersist Hfidx
  ipersist Hfsch
  ipersist Hfstop
  imodintro
  isplitl [Hcu Hq]
  · iunfold compactRight
    iframe Hcu Hq
    iunfold schedule.schedLive
    iexists n
    iframe Hn Hd
  iunfold storeStop
  iexists o
  iframe Hsc Hr Hph
  isplitr
  · iunfold curAt; iexact Hc
  iunfold storeFields
  iframe Hfb Hfidx Hfsch Hfstop

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
    Perennial.EtcdGrove.mvcc.readerPool_withPhys, Perennial.EtcdGrove.mvcc.wDep_withPhys, Perennial.EtcdGrove.mvcc.wsDep_withPhys, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_clog, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_leases, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_revs, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_cok, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_watchQ, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_wr, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_cur, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_rst, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tk, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tko, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_wsd, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tkw, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_tkr, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_idx_hist, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_idx_log, Perennial.EtcdGrove.mvcc.StoreNames.withPhys_idx_crev])

section physShare
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.revMu`'s resource, not restoring, at a share's names** (D22 receiver epochs, S5b): a share
of the fields at `γ.withPhys p`'s names (the watchable store's, a reader's) finds the lock's body at
them, the logical parts of `γ`. -/
theorem revMuInv_open_share (s : Loc) (γ : StoreNames) (p : PhysNames) (q q' : Qp)
    (o : StoreObjs) :
    revMuInv (GF := GF) s γ q ∗ fieldShareAt s (γ.withPhys p) q' o ⊢
      revMuBody s γ (γ.withPhys p) q ∗ revMuTok γ (γ.withPhys p) q ∗
        fieldShareAt s (γ.withPhys p) q' o := by
  iintro ⟨H, Hf⟩
  iunfold fieldShareAt at Hf
  iNamed Hf
  ihave Hfrst : dghostVar (GF := GF) γ.rst (DFrac.own q'.half) false $$ [Hfrst]
  · withPhys_simp; iexact Hfrst
  icases revMuInv_open_pin s γ p q _ _ o $$ [H Hfrst Hcur] with ⟨H, Htk, Hfrst, Hcur⟩
  · iframe H Hfrst Hcur
  iframe H Htk
  iunfold fieldShareAt
  simp only [named]
  withPhys_simp
  iframe Hcur Hflds Hfrst Hph

end physShare

end mvcc
end EtcdGrove
end Perennial
