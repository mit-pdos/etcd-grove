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
room for the tokens it holds (`store.Read`).
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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevOrder
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

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

/-- The backend's parameters of a real instance: the hook's buckets all but `Key`, `Key` the one
safe-range bucket, the hook's own keys the consistent index's two in `Meta` (2026-10-13, unit 7:
only the server's pre-commit hook writes them). -/
def KBReal.P (d : KBReal) : backend.BParams :=
  { BT := d.BT, HB := fun n => decide (n ≠ keyName), SB := fun n => decide (n = keyName),
    HK := fun n k => decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧
      (k = go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes)),
    hookMax := d.hookMax, limit := d.limit }

/-- The ghost names of a store: its index's and its bucket's, and its backend's instance (`kb`:
`none`, mvcc's assumed backend contract over the store's own ghost map `bucket`; `some d`, the
real backend). -/
structure StoreNames where
  idx : IdxNames
  bucket : GName
  /-- `ghostVar Log`: the committed log, half under `s.revMu`, half under the batch lock -/
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
    (fun x : backend.BNames => (x.hkd, x.db, x.view, x.rd, x.hist, x.cached, x.cur, x.hook, x.opn, x.wb,
      x.rdt, x.txa, x.txb, x.rvs, x.cvw, x.wbc, x.used, x.cls, x.sdn, x.stk))
    (fun p => ⟨p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, p.1⟩)
    (fun _ => rfl)

instance kbReal_countable : Pos.Countable KBReal :=
  countableOfLeftInverse (fun x : KBReal => (x.γB, x.BT, x.hookMax, x.limit, x.be, x.gx))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩) (fun _ => rfl)

instance storeNames_countable : Pos.Countable StoreNames :=
  countableOfLeftInverse
    (fun x : StoreNames => (x.idx, x.bucket, x.clog, x.leases, x.revs, x.hook, x.hookFn, x.kb,
      x.cmeta, x.fin, x.sch))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

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
theorem mkOk_loc_inj [FfiSyntax] [GoLocalContext] [GoGlobalContext] [go.Semantics] (T : go.GoType)
    {a b : Loc}
    (h : interface.mkOk T #a = interface.mkOk T #b) : a = b := by
  unfold interface.mkOk at h
  simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact go.intoVal_inj h

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]


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

/-- The bytes of `schema.ScheduledCompactKeyName` (`"scheduledCompactRev"`). -/
def schedKeyBytes : GoString := go!"scheduledCompactRev"
/-- The bytes of `schema.FinishedCompactKeyName` (`"finishedCompactRev"`). -/
def finKeyBytes : GoString := go!"finishedCompactRev"

/-- The `Meta` bucket's two compaction keys (the store's: nothing else writes them). -/
def metaCompactKey (kn : GoString) : Prop := kn = schedKeyBytes ∨ kn = finKeyBytes

/-- A value the store writes at a compaction key (`RevToBytes(Revision{Main: x})`, `x ≥ 0`). -/
def metaRevVal (v : GoString) : Prop := ∃ x : w64, 0 ≤ sint.Z x ∧ v = revBytes ⟨x, W64 0⟩ false

/-- `rt`'s `UnsafeRange(schema.Meta, key, nil, 0)` at a compaction key: nothing, or the key and
a value the store wrote there (`metaRevVal`; which one is not modelled: the store's own record
is `metaCompact`, under the batch lock). -/
def metaReadSpec (rt : GoInterfaceOk) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (kn : GoString) (dq : DFrac),
    ⌜metaCompactKey kn⌝ →
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ key ↦*{dq} kn }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); key ↦*{dq} kn ∗
        ((ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice)) ∨
          ∃ (ksl vsl : GoSlice) (v : GoString), ks ↦*□ [ksl] ∗ ksl ↦*□ kn ∗ vs ↦*□ [vsl] ∗
            vsl ↦*□ v ∗ ⌜metaRevVal v⌝) }})

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

/-- With no key deletable, a thinned snapshot is the bucket. -/
theorem snapThin_eq (m m' : Bucket) (Del : GoString → IProp GF) :
    snapThin m m' Del ∗ □ (∀ k, Del k -∗ False) ⊢ ⌜m' = m⌝ := by
  iintro ⟨Ht, #Hno⟩
  iunfold snapThin at Ht
  icases Ht with ⟨%Hsub, #Hdel⟩
  ihave Hall : iprop(∀ (k v : GoString), ⌜m.lookup k = some v⌝ -∗ ⌜m'.lookup k = some v⌝) $$ []
  · iintro %k %v %hm
    cases hm' : m'.lookup k with
    | none =>
      ihave Hd := Hdel $$ %k %v
      ispecialize Hd $$ []
      · ipureintro; exact ⟨hm, hm'⟩
      iexfalso
      iapply Hno $$ %k Hd
    | some v' => ipureintro; rw [Hsub k v' hm'] at hm; rw [hm]
  ihave %Hall' := Hall
  ipureintro
  apply GMap.ext
  intro k
  cases hm : m.lookup k with
  | none =>
    cases hm' : m'.lookup k with
    | none => rfl
    | some v => rw [Hsub k v hm'] at hm; cases hm
  | some v => rw [Hall' k v hm]

/-- A `ReadTx` as the compaction's `checkPrevCompactionCompleted` uses it, with no view of the
bucket (it holds neither of the store's locks that hold the view): `RLock`/`RUnlock` return, and
its reads of the `Meta` bucket's compaction keys (`metaReadSpec`). -/
def metaReadTx (rt : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    □ metaReadSpec rt)

instance metaReadTx_persistent (rt : GoInterfaceOk) : Persistent (metaReadTx (GF := GF) rt) := by
  unfold metaReadTx; infer_instance

/-- `rt` locked, over the snapshot `m` of the bucket (persistent), with `Tok` the reader's
token from its `RLock` to its `RUnlock`: `RUnlock` takes `Tok` and gives back the reader's
budget token `RT` (`isKeyBackendG`), and under `Tok` its reads are the snapshot's: a key's
entry (`keyRangeSpec`) and, if `rng`, a range of keys (`keyRangeReadSpec`), their slices readable
through `Rd` while `Tok` is held (`rdCap`). (`rng` is false for a `ConcurrentReadTx`, whose range
of a safe-range bucket can return a key twice over a stale cached read buffer: 2026-10-13, unit 5,
`issues/etcd-backend-read-buffer-cache-stale-after-commit.md`.) -/
def keyReadLocked (RT : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) : IProp GF :=
  iprop(□ ({{ Tok }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); RT }}) ∗
    □ keyRangeSpec rt m Rd Tok ∗ (if rng then □ keyRangeReadSpec rt m Rd Tok else iprop(True)) ∗
    rdCap Rd Tok)

instance keyReadLocked_persistent (RT : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    Persistent (keyReadLocked RT rng rt m Rd Tok) := by
  unfold keyReadLocked; cases rng <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- A locked snapshot with its range read has it. -/
theorem keyReadLocked_range (RT : IProp GF) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    keyReadLocked (GF := GF) RT true rt m Rd Tok ⊢ □ keyRangeReadSpec rt m Rd Tok := by
  unfold keyReadLocked
  simp only [↓reduceIte]
  iintro ⟨-, -, #H, -⟩
  iexact H

/-- A locked snapshot with its range read is one without. -/
theorem keyReadLocked_weaken (RT : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    keyReadLocked (GF := GF) RT rng rt m Rd Tok ⊢ keyReadLocked RT false rt m Rd Tok := by
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
def keyReadSnap (View : Qp → Bucket → IProp GF) (RT : IProp GF) (Del : GoString → IProp GF)
    (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) : IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (m' : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
        Tok ∗ keyReadLocked RT rng rt m' Rd Tok ∗ snapThin m m' Del }}))

instance keyReadSnap_persistent (View : Qp → Bucket → IProp GF) (RT : IProp GF)
    (Del : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    Persistent (keyReadSnap View RT Del rng rt m L) := by
  unfold keyReadSnap; infer_instance

/-- A reader of the bucket `m` through `rt` (what `rangeKeys` needs of its `tx`): `rt`'s
`UnsafeRange(schema.Key, key, nil, 0)`, for `key` holding `k`, reads `k`'s entry of `m`, with
the owned resource `R` it needs (a read transaction's token; the batch transaction's lock token
and the bucket's view for a write transaction's). The slices it returns are readable through
some `Rd` while a token `T` is held, which the call gives for `R` (`T -∗ R`: the batch
transaction's state at the read, for its lock token). -/
def keyReader (rt : GoInterfaceOk) (m : Bucket) (R : IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ R ∗ key ↦*{dq} k }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); ∃ (Rd : GoSlice → GoString → IProp GF)
        (T : IProp GF), T ∗ (T -∗ R) ∗ rdCap Rd T ∗ key ↦*{dq} k ∗ keyVals Rd ks vs m k }})

instance keyReader_persistent (rt : GoInterfaceOk) (m : Bucket) (R : IProp GF) :
    Persistent (keyReader (GF := GF) rt m R) := by
  unfold keyReader; infer_instance

/-- A locked snapshot is a reader, its token owned. -/
theorem keyReadLocked_reader (RT : IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket)
    (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF) :
    keyReadLocked (GF := GF) RT rng rt m Rd Tok ⊢ keyReader rt m Tok := by
  iintro #H
  iunfold keyReadLocked at H
  icases H with ⟨-, #Hr, -, #Hcap⟩
  iunfold keyRangeSpec at Hr
  iunfold keyReader
  iintro %b %key %k %dq !> %Φ ⟨#HK, HT, Hkey⟩ HΦ
  iapply Hr $$ %b %key %k %dq %Φ [HT Hkey]
  · iframe HT Hkey; iexact HK
  inext
  iintro %ks %vs ⟨HT, Hkey, #Hkv⟩
  iapply HΦ
  iexists Rd, Tok
  iframe HT Hkey Hkv Hcap
  iintro H; iexact H

/-- What a reader of the index knows makes its log well formed and bounded (kept). -/
theorem idxKnows_wf (γ : IdxNames) (kn : IdxKnow) :
    idxKnows (GF := GF) γ kn ⊢ idxKnows γ kn ∗
      ⌜LogWf' kn.log ∧ kn.log.length < 2 ^ 63 ∧ ∀ cs ∈ kn.log, cs.length < 2 ^ 63⌝ := by
  cases kn with
  | cert log =>
    rw [idxKnows_cert]
    iintro #H
    iframe H
    iunfold idxCert at H
    icases H with ⟨-, -, %Hc, -⟩
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

/-- **The store's post-lock hook** (persistent): the backend's batch lock has invariant `P` and
its `LockInsideApply` runs the hook `f` (a Go `func()`) right after taking the lock
(`batchTx.LockInsideApply` calls `txPostLockInsideApplyHook`). `P` and `f` are fixed per store
(`NewStore` allocates the names); a saved proposition and a read-only ghost variable, so that a
caller naming them agrees with the store's (`hookIs_agree`, `hookIs_agree_lc`). -/
def hookIs (γ : StoreNames) (P : IProp GF) (f : val) : IProp GF :=
  iprop(savedPropOwn γ.hook DFrac.discard P ∗ dghostVar γ.hookFn DFrac.discard f)

instance hookIs_persistent (γ : StoreNames) (P : IProp GF) (f : val) :
    Persistent (hookIs γ P f) := by
  unfold hookIs; infer_instance

/-- Two views of the hook agree: the same function, the same invariant a step later. -/
theorem hookIs_agree (γ : StoreNames) (P P' : IProp GF) (f f' : val) :
    hookIs γ P f ∗ hookIs γ P' f' ⊢ ⌜f = f'⌝ ∗ ▷ (P ≡ P') := by
  iintro ⟨H1, H2⟩
  iunfold hookIs at H1 H2
  icases H1 with ⟨HP1, Hf1⟩
  icases H2 with ⟨HP2, Hf2⟩
  ihave %Hf := dghostVar_agree γ.hookFn f DFrac.discard f' DFrac.discard $$ Hf1 Hf2
  ihave Heq := saved_prop_agree γ.hook DFrac.discard DFrac.discard P P' $$ HP1 HP2
  iframe Heq
  ipureintro; exact Hf

/-- **The critical-section contract** of a writing call under the store's batch lock with
invariant `P` and post-lock hook `f` (the shape of the server's `apply.Apply` contract): the
caller's `Pre`, the hook's triple from it (`{P ∗ Pre} f() {Q}`, run by `LockInsideApply`), and
the caller's update `Q ={⊤}=∗ P ∗ Post`, applied after the writes, before `Unlock` (which
takes `P` back). The call returns `Post` if it took the lock, else `Pre`. -/
def csContract (P : IProp GF) (f : val) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
    (Q ={⊤}=∗ P ∗ Post))

/-- **The no-hook instance**: with invariant `True` and a hook that does nothing
(`{True} f() {True}`), any `Pre` is its own contract (`Q = Post = Pre`). -/
theorem csContract_noHook (f : val) (Pre : IProp GF) :
    □ ({{ True }} (App (Val f) (Val #())) {{ RET #(); True }}) ∗ Pre ⊢
      csContract iprop(True) f Pre Pre Pre := by
  iintro ⟨#Hf, Hpre⟩
  iunfold csContract
  iframe Hpre
  isplitr
  · iintro !> %Φ !> ⟨-, Hpre⟩ HΦ
    iapply Hf $$ %Φ [] [Hpre HΦ]
    · itrivial
    inext
    iintro -
    iapply HΦ
    iexact Hpre
  · iintro Hq
    imodintro
    iframe Hq

/-! ## The batch transaction -/

/-- The entries a batch transaction has put into the `Key` bucket since it was locked, in
order (`UnsafeSeqPut`). -/
abbrev Puts := List (GoString × GoString)

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

**Compaction** (2026-10-13, unit 5a; `notes/decisions.md`, "mvcc: compaction"):
`LockOutsideApply()` with the deposit witness `Dep` (`batchTxInitSpec`'s first `Unlock` returns
it) gives `W` (the compaction job's lock, after `NewStore`). Where the backend supports mvcc's
compaction (`Cmp`): `UnsafeDelete(schema.Key, k)` of a key compaction may delete (`Del k`, the
store's choice: `delKey`) leaves the token as it is (the logical bucket the view holds is not
changed: the deletion shows only in what later reads may miss, `snapThin`);
`UnsafeRange(schema.Key, lo, hi, limit)` with a positive limit reads the first `limit` entries in
`[klo, khi)`, in key order, of the bucket with the puts so far, some keys compaction may delete
missing (read-only slices); `UnsafePut(schema.Meta, k, v)` at a compaction key
(`metaCompactKey`) of a value the store writes there (`metaRevVal`) leaves the token as it is
(the store's record of the meta keys is its own, `metaCompact`).

The store's instance over mvcc's assumed backend (`batchTxSpec`) has no tokens (`RT = WT =
True`), no condition and `Cmp`: the backend's bridge (`BackendBridge.lean`) proves the general
one with the backend's, `Cmp` false (2026-10-13, unit 4; the merge with the compaction). -/
def batchTxSpecG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF) (P : IProp GF) (f : val) :
    IProp GF :=
  iprop(□ (∀ (Pre Q : IProp GF),
      {{ Pre ∗ RT ∗ WT ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
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
    □ (⌜Cmp⌝ -∗ ∀ (l : Puts) (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked l ∗ Del k ∗
          key ↦*{dq} k }}
        (App (App (Val #(methods bt.ty go!"UnsafeDelete" bt.v)) (Val #b)) (Val #key))
      {{ RET #(); Locked l ∗ key ↦*{dq} k }}) ∗
    □ (⌜Cmp⌝ -∗ ∀ (l : Puts) (q : Qp) (m : Bucket) (b : GoInterface) (lo hi : GoSlice)
        (klo khi : GoString) (limit : w64) (dqlo dqhi : DFrac),
      ⌜0 < sint.Z limit ∧ khi ≠ []⌝ →
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked l ∗ View q m ∗
          lo ↦*{dqlo} klo ∗ hi ↦*{dqhi} khi }}
        (App (App (App (App (Val #(methods bt.ty go!"UnsafeRange" bt.v)) (Val #b)) (Val #lo))
          (Val #hi)) (Val #limit))
      {{ (ks vs : GoSlice), RET (PairV #ks #vs); Locked l ∗ View q m ∗ lo ↦*{dqlo} klo ∗
          hi ↦*{dqhi} khi ∗
          ∃ m' : Bucket, snapThin (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) m' Del ∗
            pairVals (fun s b => iprop(s ↦*□ b)) ks vs
              ((bucketRange m' klo khi).take (sint.Z limit).toNat) }}) ∗
    □ (⌜Cmp⌝ -∗ ∀ (l : Puts) (b : GoInterface) (key val : GoSlice) (k v : GoString)
        (dq dq' : DFrac),
      ⌜metaCompactKey k ∧ metaRevVal v⌝ →
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Meta ↦□ b ∗ Locked l ∗
          key ↦*{dq} k ∗ val ↦*{dq'} v }}
        (App (App (App (Val #(methods bt.ty go!"UnsafePut" bt.v)) (Val #b)) (Val #key))
          (Val #val))
      {{ RET #(); Locked l ∗ key ↦*{dq} k ∗ val ↦*{dq'} v }}))

instance batchTxSpecG_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF)
    (P : IProp GF) (f : val) :
    Persistent (batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P f) := by
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
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (f : val) : IProp GF :=
  iprop(∃ (Locked : Puts → IProp GF) (LockedO : Nat → IProp GF),
    batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P f ∗
      batchTxInitSpec bt RT WT W Wi Dep LockedO P)

instance isBatchTxG_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (f : val) :
    Persistent (isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P f) := by
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
    (W Dep : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF) (f : val) : IProp GF :=
  batchTxSpecG bt View iprop(True) iprop(True) noPutCond Del W Dep True Locked P f

instance batchTxSpec_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF)
    (f : val) : Persistent (batchTxSpec bt View Del W Dep Locked P f) := by
  unfold batchTxSpec; infer_instance

/-- `bt` is a batch transaction (mvcc's assumed backend). -/
def isBatchTx (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (P : IProp GF) (f : val) : IProp GF :=
  isBatchTxG bt View iprop(True) iprop(True) noPutCond Del W iprop(True) Dep True P f

/-- The batch transaction under its lock is a reader of its own puts over the view, when no key
is deletable (`□ (Del k ={⊤}=∗ False)`: no compaction). -/
theorem batchTx_reader (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF) (P : IProp GF) (f : val)
    (l : Puts) (q : Qp) (m : Bucket) :
    batchTxSpecG bt View RT WT PutOk Del W Dep Cmp Locked P f ∗ □ (∀ k, Del k ={⊤}=∗ False) ⊢
      keyReader bt (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) iprop(Locked l ∗ View q m) := by
  iintro ⟨#H, #Hno⟩
  iunfold batchTxSpecG at H
  icases H with ⟨-, -, -, -, #Hr, -⟩
  iunfold keyReader
  iintro %b %key %k %dq !> %Φ ⟨#HK, ⟨Hl, Hv⟩, Hkey⟩ HΦ
  iapply wp_fupd
  iapply Hr $$ %l %q %m %b %key %k %dq [Hl Hv Hkey]
  · iframe Hl Hv Hkey; iexact HK
  inext
  iintro %ks %vs ⟨%Rd, %T, HT, Hback, #Hcap, Hv, Hkey, Hkv⟩
  icases Hkv with (#Hkv | ⟨Hd, -⟩)
  rotate_left
  · ispecialize Hno $$ %k Hd
    imod Hno with %Hf
    exact Hf.elim
  imodintro
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

/-- The store's batch transaction under its lock is a reader of its own puts over the view. -/
theorem batchTxSpec_reader (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF)
    (f : val) (l : Puts) (q : Qp) (m : Bucket) :
    batchTxSpec bt View Del W Dep Locked P f ∗ □ (∀ k, Del k ={⊤}=∗ False) ⊢
      keyReader bt (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) iprop(Locked l ∗ View q m) := by
  unfold batchTxSpec
  exact batchTx_reader bt View _ _ _ Del W Dep _ Locked P f l q m

instance isBatchTx_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (Del : GoString → IProp GF) (W Dep : IProp GF) (P : IProp GF) (f : val) :
    Persistent (isBatchTx bt View Del W Dep P f) := by
  unfold isBatchTx; infer_instance

/-- `b` is a `Backend` whose `ConcurrentReadTx()` and `ReadTx()`, for a reader's token `RT`
(the backend's readers are bounded: a slot of its read lock and of its `txMu`, a budget token,
and the backend open; given back by the reader's `RUnlock`), return a snapshot reader of the
bucket the caller holds as `View q m` (any fraction `q`), which the caller keeps, with the right
`L` to lock it (`keyReadSnap`: its `RLock` gives the reader's token, its `RUnlock` takes it),
and whose `BatchTx()` is a batch transaction over the view, its lock holding `W`;
`ForceCommit()`, for a session's token `WT` (`RT` lent), returns (the commit to disk has no
effect on the view); `Size()`/`SizeInUse()` return some number. The snapshots may miss keys
compaction may have deleted (`Del`, `snapThin`), and the batch transaction's lock, after
`NewStore`'s first `Unlock`, holds `W` with the deposit witness `Dep` (persistent, its own).
Where the backend supports mvcc's compaction (`Cmp`): the job's calls, with no effect on the
model, `LockForSafeRangeDelete()`/`UnlockForSafeRangeDelete()` (the defragmentation's exclusion)
and `ReadTx()` with no view, for the reads of the `Meta` bucket's compaction keys alone
(`metaReadTx`: `checkPrevCompactionCompleted`). The instance of mvcc's assumed backend
(`isKeyBackend`) has no tokens, no condition on the puts (`batchTxSpecG`'s `PutOk`) and `Cmp`;
`BackendBridge.lean` proves the general one of the backend, `Cmp` false (2026-10-13, unit 4; the
merge with the compaction, unit 5a). -/
def isKeyBackendG (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (f : val) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnap View RT Del false rt m L }}) ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnap View RT Del true rt m L }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt);
          isBatchTxG bt View RT WT PutOk Del W Wi Dep Cmp P f }}) ∗
    □ ({{ RT ∗ WT }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      {{ RET #(); RT }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"Size" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"SizeInUse" bi.v)) (Val #()))
      {{ (n : w64), RET #n; True }}) ∗
    □ (⌜Cmp⌝ -∗
      □ ({{ True }} (App (Val #(methods bi.ty go!"LockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); True }}) ∗
      □ ({{ True }} (App (Val #(methods bi.ty go!"UnlockForSafeRangeDelete" bi.v)) (Val #()))
        {{ RET #(); True }}) ∗
      □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
        {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); metaReadTx rt }})))

instance isKeyBackendG_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (f : val) :
    Persistent (isKeyBackendG b View RT WT PutOk Del W Wi Dep Cmp P f) := by
  unfold isKeyBackendG; infer_instance

/-- mvcc's assumed backend contract: no tokens, no condition on the puts, nothing in the lock
before `NewStore`'s first `Unlock`, the compaction's calls (its deposit witness its own). -/
def isKeyBackend (b : GoInterface) (View : Qp → Bucket → IProp GF) (Del : GoString → IProp GF)
    (W : IProp GF) (P : IProp GF) (f : val) : IProp GF :=
  iprop(∃ Dep : IProp GF,
    isKeyBackendG b View iprop(True) iprop(True) noPutCond Del W iprop(True) Dep True P f)

instance isKeyBackend_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (Del : GoString → IProp GF) (W : IProp GF) (P : IProp GF) (f : val) :
    Persistent (isKeyBackend b View Del W P f) := by
  unfold isKeyBackend; infer_instance

/-! ## The lessor

(2026-10-13, unit 8 of the backend: the lessor's KV-facing methods are proved,
`Proof/go_etcd_io/etcd/server/v3/lease/`; this contract is derived from them,
`lease.isLessor_of_lessorInv`.) A lease is live for the holder of the lease owner's half of the
lessor's live set (`lease.leaseOwn γl L`: `L`), not for good: `Revoke` shrinks `L`, after which
`Attach` returns `ErrLeaseNotFound` (on which mvcc's `put` panics). So `Attach` takes the
owner's half and the lease's membership, and `GetLease` a reader slot of the lessor's lock
(`lease.lessorRd`; the store keeps one, `lessorRdOf` in its writer's resource). -/

/-- The lessor `le` (the real `*lessor` at `lp`, ghost map `γl`), as the KV core uses it:
`GetLease(item)` returns some lease id (`NoLease` if none), with a reader slot; `Attach(id,
items)` of a live lease (`id ∈ L`, the owner's half held) returns `nil`; `Detach(id, items)`
returns `nil` or an error (which the code logs). The items are read. `SetRangeDeleter(f)`
returns: `NewStore` passes the closure `func() lease.TxnDelete { return s.Write(traceutil.TODO())
}` (the store's own verified `store.Write`), which the contract takes as an opaque value; the
lessor's later calls of it (`Revoke`) are outside the model. The lessor's ghost name `γl` is its
own (it exists before the store). -/
def isLessor (le : GoInterface) (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, ⌜le = lease.lessorIface lp⌝ ∗ lease.lessorPin γl lp ∗
    □ (∀ (item : go_etcd_io.etcd.server.v3.lease.LeaseItem),
      {{ lease.lessorRd lp γl }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"GetLease" #lp)) (Val #item))
      {{ (id : w64), RET #id; lease.lessorRd lp γl }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac) (L : List w64),
      {{ lease.leaseOwn γl L ∗ ⌜id ∈ L⌝ ∗ items ↦*{dq} l }}
        (App (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"Attach" #lp)) (Val #id)) (Val #items))
      {{ RET #(GoInterface.nil); lease.leaseOwn γl L ∗ items ↦*{dq} l }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac),
      {{ items ↦*{dq} l }}
        (App (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"Detach" #lp)) (Val #id)) (Val #items))
      {{ (err : GoInterface), RET #err; items ↦*{dq} l }}) ∗
    □ (∀ f : GoFunc,
      {{ True }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty)
          go!"SetRangeDeleter" #lp)) (Val #f))
      {{ RET #(); True }}))

instance isLessor_persistent (le : GoInterface) (γl : GName) : Persistent (isLessor (GF := GF) le γl) := by
  unfold isLessor; infer_instance

/-- Halving distributes over a sum of fractions. -/
theorem qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

/-! ## The backend instances (2026-10-13, unit 5)

The store is over one of two backends, named by its `StoreNames.kb`: mvcc's assumed contract
(`none`: the view is the store's own ghost map, no tokens, no condition on the puts, `W` the
writer's resource itself) or the real backend (`some d`: the backend's clients' view of the `Key`
bucket, a reader's slot of the backend and a share of it open, a write-back's budget, the
safe-range condition on the puts, and the batch lock's late-bound resource `lateW`). -/

/-- The readers' view `vd` of the backend is the `Key` bucket `m`, and nothing else. -/
def keyView (vd : backend.VData) (m : Bucket) : Prop :=
  ∀ n k, vd.lookup (n, k) = if n = keyName then m.lookup k else none

/-- One `keyView` per view. -/
theorem keyView_inj {vd : backend.VData} {m m' : Bucket} (h : keyView vd m) (h' : keyView vd m') :
    m = m' := by
  apply GMap.ext
  intro k
  have a := h keyName k
  have b := h' keyName k
  simp only [↓reduceIte] at a b
  rw [← a, ← b]

/-- mvcc's view of the `Key` bucket over the real backend, at fraction `q`: the backend's
clients' view (`bView`) of it. -/
def bkView (γB : backend.BNames) (q : Qp) (m : Bucket) : IProp GF :=
  iprop(∃ vd : backend.VData, backend.bView γB q vd ∗ ⌜keyView vd m⌝)

/-- The view of the bucket in the instance `kb` (`γb` the store's ghost map, for `none`). -/
def kbView (kb : Option KBReal) (γb : GName) (q : Qp) (m : Bucket) : IProp GF :=
  match kb with
  | none => ghostMapAuth γb q m
  | some d => bkView d.γB q m

/-- A reader's token in the instance `kb`: for the real backend, a reader's slot of it and a
share of it open (given back at the reader's `RUnlock`). -/
def kbRT (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => iprop(backend.rdTok d.γB d.P d.be ∗ ∃ q : Qp, backend.bOpen d.γB q)

/-- A write session's token in the instance `kb`: for the real backend, a write-back's budget
(every `Unlock` may increment the read buffer's version, a `uint64`: `backend.wbTok`). -/
def kbWT (kb : Option KBReal) : IProp GF :=
  match kb with
  | none => iprop(True)
  | some d => backend.wbTok d.γB

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

/-- The store's reader token (`kbRT`). -/
abbrev storeRT (γ : StoreNames) : IProp GF := kbRT γ.kb

/-- The store's write token (`kbWT`): `store.Write` spends one. -/
abbrev storeWT (γ : StoreNames) : IProp GF := kbWT γ.kb

/-- The store's condition on its backend's puts (`kbPutOk`). -/
abbrev storePutOk (γ : StoreNames) : Bucket → Puts → GoString → GoString → Prop := kbPutOk γ.kb

/-- The store's bound on a write transaction's changes (`kbPutMax`). -/
abbrev putMax (γ : StoreNames) : Nat := kbPutMax γ.kb

theorem putMax_le (γ : StoreNames) : putMax γ ≤ 2 ^ 63 := kbPutMax_le γ.kb

theorem putMax_ge (γ : StoreNames) : 2 ^ 56 ≤ putMax γ := by
  unfold putMax kbPutMax; cases γ.kb <;> simp

/-- Whether the backend of the instance `kb` supports mvcc's compaction (`isKeyBackendG`'s
`Cmp`): mvcc's assumed backend does; the real backend does not yet (its model forbids deleting
from the safe-range `Key` bucket, and an `Unlock` that changes what readers see needs the
clients' whole view, which the compaction job, under the batch lock alone, does not hold;
`notes/decisions.md`, "The compaction over the real backend"). -/
def kbCmp (kb : Option KBReal) : Prop := kb = none

/-- The store's backend supports compaction (`kbCmp`). -/
abbrev storeCmp (γ : StoreNames) : Prop := kbCmp γ.kb

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
      simp only
      unfold bkView backend.bView
      rw [qp_half_add]
      constructor
      · iintro ⟨%vd, ⟨Hv, Hc⟩, %Hk⟩
        icases (hv vd).1 $$ Hv with ⟨Hv1, Hv2⟩
        icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
        isplitl [Hv1 Hc1]
        · iexists vd; iframe; ipureintro; exact Hk
        · iexists vd; iframe; ipureintro; exact Hk
      · iintro ⟨⟨%vd1, ⟨Hv1, Hc1⟩, %Hk1⟩, ⟨%vd2, ⟨Hv2, Hc2⟩, %Hk2⟩⟩
        ihave %Heq := ghostVar_agree d.γB.view vd1 _ vd2 _ $$ Hv1 Hv2
        subst Heq
        iexists vd1
        isplitl [Hv1 Hv2 Hc1 Hc2]
        · isplitl [Hv1 Hv2]
          · iapply (hv vd1).2; iframe
          · iapply hc.2; iframe
        ipureintro; exact Hk1

/-- The view as two halves (`s.revMu`'s and the batch lock's). -/
theorem bucketView_halves (γ : StoreNames) (q : Qp) (m : Bucket) :
    bucketView (GF := GF) γ q m ⊣⊢ bucketView γ q.half m ∗ bucketView γ q.half m := by
  have h := (bucketView_fractional (GF := GF) γ m).fractional q.half q.half
  rw [Qp.half_add_half] at h
  exact h

/-- Two parts of the view agree on the bucket. -/
theorem bucketView_agree (γ : StoreNames) (q1 q2 : Qp) (m1 m2 : Bucket) :
    bucketView (GF := GF) γ q1 m1 ∗ bucketView γ q2 m2 ⊢ ⌜m1 = m2⌝ := by
  unfold bucketView kbView
  cases γ.kb with
  | none =>
    simp only
    iintro ⟨H1, H2⟩
    iapply ghostMapAuth_agree $$ H1 H2
  | some d =>
    simp only
    unfold bkView backend.bView
    iintro ⟨⟨%vd1, ⟨Hv1, -⟩, %Hk1⟩, ⟨%vd2, ⟨Hv2, -⟩, %Hk2⟩⟩
    ihave %Heq := ghostVar_agree d.γB.view vd1 _ vd2 _ $$ Hv1 Hv2
    subst Heq
    ipureintro; exact keyView_inj Hk1 Hk2

/-- A revision token: the right to open one write transaction (`store.Write`). The store's
`NewStore` hands out `2 ^ 63 - 5` of them: with the budget `writerRes` keeps, the revision
counter stays below `2 ^ 63 - 2`. -/
def revToken (γ : StoreNames) : IProp GF := ownToks γ.revs 1

/-- A full fraction as two halves (for `currentRev`, half under `s.revMu`, half the writer's). -/
theorem own_half_half (q : Qp) : (DFrac.own q : DFrac) = DFrac.own q.half • DFrac.own q.half := by
  have h := Qp.half_add_half q
  calc (DFrac.own q : DFrac) = DFrac.own (q.half + q.half) := by rw [h]
    _ = DFrac.own q.half • DFrac.own q.half := rfl

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
  rw [ownTokAuth, own_half_half]
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

instance compactTok_timeless (γ : StoreNames) (c : Int) :
    Timeless (compactTok (GF := GF) γ c) := by
  unfold compactTok idxCompactor; infer_instance

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
the queue there) and returns it at the new revision. -/
def compactRight (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(crevUB γ.idx (1 : Qp).half c ∗ compactQueue γ c)

/-- The invariant's name of a frozen compaction revision. -/
abbrev crevFrozenN : Namespace := nroot.@"mvcc_crevFrozen"

/-- **No compaction, ever** (persistent): the compaction right at `-1`, given up into an
invariant (`compactRight_freeze`; its half of the revision's authority, the jobs' queue dropped),
so the revision stays `-1` (no one can gather the authority
to update it). The store's readers and writers as the txn, apply, request path and watchable
store use them (`storeReader`) carry it: their specs are of a store that is not compacted. -/
def crevFrozen (γ : StoreNames) : IProp GF := inv crevFrozenN (crevUB γ.idx (1 : Qp).half (-1))

instance crevFrozen_persistent (γ : StoreNames) : Persistent (crevFrozen (GF := GF) γ) := by
  unfold crevFrozen; infer_instance

/-- **A key compaction may delete** (persistent, the store's choice of the backend contract's
`Del`): of a certified log, a revision's bytes compaction at a lower bound `c` of the
compaction revision may delete (`KeyDel`, `Compact.lean`). -/
def delKey (γ : StoreNames) (k : GoString) : IProp GF :=
  iprop(∃ (c : Int) (log : Log), crevLb γ.idx c ∗ idxCert γ.idx log ∗ ⌜-1 ≤ c ∧ KeyDel log c k⌝)

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

/-- With a part of the compaction revision's authority at `-1`, no key is deletable. -/
theorem crevUB_noDel (γ : StoreNames) (q : Qp) (k : GoString) :
    ⊢ crevUB (GF := GF) γ.idx q (-1) -∗ delKey γ k -∗ False := by
  iintro Hc Hd
  iunfold delKey at Hd
  icases Hd with ⟨%c, %log, #Hlb, -, %Hk⟩
  ihave %Hle := crevUB_lb γ.idx q (-1) c (by decide) Hk.1 $$ Hc Hlb
  exact (KeyDel_neg (show c < 0 by omega) Hk.2).elim

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

/-- **Freezing**: the compaction right at `-1` given up (no compaction, ever). -/
theorem compactRight_freeze (γ : StoreNames) (E : CoPset) :
    ⊢ compactRight (GF := GF) γ (-1) ={E}=∗ crevFrozen γ := by
  iintro H
  iunfold compactRight at H
  icases H with ⟨H, -⟩
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

/-- **A frozen store deletes nothing.** -/
theorem crevFrozen_noDel (γ : StoreNames) (k : GoString) :
    ⊢ crevFrozen (GF := GF) γ -∗ delKey γ k ={⊤}=∗ False := by
  iintro #Hf #Hd
  iunfold crevFrozen at Hf
  imod inv_acc (E := ⊤) (N := crevFrozenN) (P := crevUB (GF := GF) γ.idx (1 : Qp).half (-1))
    (by exact CoPset.subseteq_top) $$ Hf with ⟨>Hr, Hclose⟩
  ihave %Hf := crevUB_noDel γ (1 : Qp).half k $$ Hr Hd
  exact Hf.elim

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


/-- The batch lock's resource for the store (`W` of `isKeyBackend`): the index writer's handle
at the committed log `ilog` with no pending change, half the committed-log ghost variable (the
other half under `s.revMu`), half of `currentRev` (`store.Write` reads it under the batch lock
alone), half the bucket's view (the other half under `s.revMu`: the write transaction's reads
of the bucket, through the batch transaction), the certificate of `ilog`, and half the
revision budget's authority (the other half under `s.revMu`); and the compaction's part
(`compactRes`: the meta keys' record, the finished compactions' counter). -/
def writerRes (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (ilog : Log) (ntok : Nat),
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hw" ∷ idxWriter γ.idx ilog [] ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap ilog) ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hcres" ∷ compactRes γ ∗
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

/-- **The store's backend contract over mvcc's assumed backend** (`storeCmp γ`, `γ.kb = none`;
2026-10-13, unit 5c): no tokens, no condition on the puts, the lock resource the writer's
(`writerRes`), the compaction's calls (`Cmp` true). -/
theorem isKeyBackendG_cmp (b : GoInterface) (s : Loc) (γ : StoreNames) (Dep P : IProp GF) (f : val)
    (h : storeCmp γ) :
    isKeyBackendG (GF := GF) b (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) P f ⊢
    isKeyBackendG b (bucketView γ) iprop(True) iprop(True) noPutCond (delKey γ) (writerRes s γ)
      iprop(True) Dep True P f := by
  unfold storeCmp kbCmp at h
  unfold storeW kbWi storeRT storeWT storePutOk storeCmp kbCmp kbRT kbWT kbPutOk
  simp only [h]
  exact .rfl

/-- **The store's batch transaction over mvcc's assumed backend** (`storeCmp γ`): the assumed
contract (`batchTxSpec`), its lock resource the writer's (2026-10-13, unit 5c). -/
theorem batchTxSpecG_cmp (bt : GoInterfaceOk) (s : Loc) (γ : StoreNames) (Dep : IProp GF)
    (Locked : Puts → IProp GF) (P : IProp GF) (f : val) (h : storeCmp γ) :
    batchTxSpecG (GF := GF) bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked P f ⊢
    batchTxSpec bt (bucketView γ) (delKey γ) (writerRes s γ) Dep Locked P f := by
  unfold storeCmp kbCmp at h
  unfold batchTxSpec storeW storeRT storeWT storePutOk storeCmp kbCmp kbRT kbWT kbPutOk
  simp only [h]
  exact .rfl

/-- `s.revMu`'s resource at fraction `q`: the committed log `log`'s last revision in
`currentRev` (half of it: the writer holds the other half under the batch lock), half the
committed-log ghost variable, the index's certificate of `log` and the bucket's authority
(`bucketMap log`, half of it: the batch lock holds the other half), half the revision
budget's authority with its bound for `log`, and half the committed log's authority (the index
writer holds the other half); and the compaction revision `c` (at most the committed log's
last revision): half `compactMainRev`'s points-to and a quarter of its authority (`s.mu` holds
as much: `store.Compact`, holding both locks, updates them; the watchable store's
`syncWatchers` reads it under `s.revMu`, a transaction's `rangeKeys` under `s.mu`). -/
def revMuInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (log : Log) (ntok : Nat) (c : Int),
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketView γ q.half (bucketMap log) ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own q.half) ntok ∗
    "%Hbudget" ∷ ⌜log.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlog" ∷ idxLogAuth γ.idx q.half log ∗
    "Hcmp" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 c : w64) : IProp GF) ∗
    "Hcrev" ∷ crevUB γ.idx q.half.half c ∗
    "%Hc" ∷ ⌜-1 ≤ c ∧ c < log.length⌝)

/-- `s.revMu`'s resource is fractional (for `sync.init_RWMutex`): the halves of `currentRev`,
of the ghost log and of the bucket's view split, and two parts agree on the log. -/
instance revMuInv_fractional (s : Loc) (γ : StoreNames) : Fractional (revMuInv (GF := GF) s γ) where
  fractional q1 q2 := by
    have hcur : ∀ v : w64, (s.[store, go!"currentRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"currentRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"currentRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hclog := fun (log : Log) =>
      (ghostVar_fractional (GF := GF) γ.clog log).fractional q1.half q2.half
    have hbv := fun (m : Bucket) =>
      (bucketView_fractional (GF := GF) γ m).fractional q1.half q2.half
    have htk : ∀ n : Nat, ownTokAuthDfrac (GF := GF) γ.revs (DFrac.own (q1.half + q2.half)) n ⊣⊢
        ownTokAuthDfrac γ.revs (DFrac.own q1.half) n ∗ ownTokAuthDfrac γ.revs (DFrac.own q2.half) n :=
      fun n => ownTokAuthDfrac_split (GF := GF) γ.revs (DFrac.own q1.half) (DFrac.own q2.half) n
    have hlg := fun (log : Log) =>
      (monoListAuthOwn_fractional (GF := GF) γ.idx.log log).fractional q1.half q2.half
    have hcmp : ∀ v : w64, (s.[store, go!"compactMainRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"compactMainRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"compactMainRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hcrev := fun (c : Int) => crevUB_split (GF := GF) γ.idx q1.half.half q2.half.half c
    unfold revMuInv
    rw [qp_half_add, qp_half_add]
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

/-- `s.mu`'s resource at fraction `q`, at the compaction revision `c` (`-1`: none): half
`compactMainRev`'s points-to and a quarter of the compaction revision's authority (`s.revMu`
holds as much; the compaction right, half the authority, is `compactRight`), with a certified
log of which `c` is a revision. A transaction holds `s.mu` shared for its whole life, so its
`rangeKeys` reads `compactMainRev` from its part (`muHeld`). -/
def muInvAt (s : Loc) (γ : StoreNames) (q : Qp) (c : Int) : IProp GF :=
  iprop("HcmpM" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q.half} (W64 c : w64) : IProp GF) ∗
    "HcrevM" ∷ crevUB γ.idx q.half.half c ∗
    "#HclM" ∷ (∃ log₀ : Log, idxCert γ.idx log₀ ∗ ⌜c < log₀.length⌝) ∗
    "%HcM" ∷ ⌜-1 ≤ c⌝)

/-- `s.mu`'s resource at fraction `q`: at some compaction revision. -/
def muInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF := iprop(∃ c : Int, muInvAt s γ q c)

instance muInv_fractional (s : Loc) (γ : StoreNames) : Fractional (muInv (GF := GF) s γ) where
  fractional q1 q2 := by
    have hcmp : ∀ v : w64, (s.[store, go!"compactMainRev"] ↦{DFrac.own (q1.half + q2.half)} v :
        IProp GF) ⊣⊢ s.[store, go!"compactMainRev"] ↦{DFrac.own q1.half} v ∗
          s.[store, go!"compactMainRev"] ↦{DFrac.own q2.half} v :=
      fun v => (typedPointsto_dfractional (GF := GF) _ v).dfractional (DFrac.own q1.half)
        (DFrac.own q2.half)
    have hcrev := fun (c : Int) => crevUB_split (GF := GF) γ.idx q1.half.half q2.half.half c
    unfold muInv muInvAt
    rw [qp_half_add, qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro H
      icases H with ⟨%c, H⟩
      iNamed H
      icases (hcmp _).1 $$ HcmpM with ⟨Hm1, Hm2⟩
      icases (hcrev c).1 $$ HcrevM with ⟨Hv1, Hv2⟩
      isplitl [Hm1 Hv1]
      · iexists c; simp only [named]; iframe Hm1 Hv1; iframe #; ipureintro; exact HcM
      · iexists c; simp only [named]; iframe Hm2 Hv2; iframe #; ipureintro; exact HcM
    · iintro ⟨H1, H2⟩
      icases H1 with ⟨%c, H1⟩
      icases H2 with ⟨%c2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      ihave %Hcc := crevUB_agree γ.idx _ _ c c2 HcM1 HcM2 $$ HcrevM1 HcrevM2
      subst Hcc
      iexists c
      simp only [named]
      isplitl [HcmpM1 HcmpM2]
      · iapply (hcmp _).2; iframe HcmpM1 HcmpM2
      isplitl [HcrevM1 HcrevM2]
      · iapply (hcrev c).2; iframe HcrevM1 HcrevM2
      isplitr
      · iexact HclM1
      ipureintro; exact HcM1

/-- `s.mu` held shared by a transaction, at the compaction revision `c`: the reader's token and
its part of `s.mu`'s resource (given back at `End`). -/
def muHeld (s : Loc) (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(sync.ownRWMutexRLocked (muAddr s) (muInv s γ) ∗ muInvAt s γ sync.rfrac c)

/-- A transaction's part of the compaction revision's authority, lent (to the index's reads). -/
theorem muHeld_crev (s : Loc) (γ : StoreNames) (c : Int) :
    muHeld (GF := GF) s γ c ⊢
      crevUB γ.idx sync.rfrac.half.half c ∗ (crevUB γ.idx sync.rfrac.half.half c -∗ muHeld s γ c) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha⟩
  iunfold muInvAt at Ha
  iNamed Ha
  iframe HcrevM
  iintro Hc
  iunfold muHeld
  iframe Hl
  iunfold muInvAt
  iframe HcmpM Hc
  iframe #
  ipureintro; exact HcM

/-- A transaction's part of `compactMainRev` and of the compaction revision's authority, lent (to
`rangeKeys`), with the revision's bounds. -/
theorem muHeld_cmp (s : Loc) (γ : StoreNames) (c : Int) :
    muHeld (GF := GF) s γ c ⊢
      (s.[store, go!"compactMainRev"] ↦{DFrac.own sync.rfrac.half} (W64 c : w64) : IProp GF) ∗
      crevUB γ.idx sync.rfrac.half.half c ∗ ⌜-1 ≤ c ∧ c < 2 ^ 63⌝ ∗
      ((s.[store, go!"compactMainRev"] ↦{DFrac.own sync.rfrac.half} (W64 c : w64) : IProp GF) -∗
        crevUB γ.idx sync.rfrac.half.half c -∗ muHeld s γ c) := by
  iintro H
  iunfold muHeld at H
  icases H with ⟨Hl, Ha⟩
  iunfold muInvAt at Ha
  iNamed Ha
  ihave #Hcl := HclM
  icases Hcl with ⟨%log₀, #Hc0, %Hlt⟩
  iunfold idxCert at Hc0
  icases Hc0 with ⟨-, -, %Hwf, -⟩
  iframe HcmpM HcrevM
  isplitl []
  · ipureintro; exact ⟨HcM, by omega⟩
  iintro Hm Hc
  iunfold muHeld
  iframe Hl
  iunfold muInvAt
  iframe Hm Hc
  iframe #
  ipureintro; exact HcM

/-- A store (persistent): its backend (of its instance `γ.kb`, registered; with the batch lock's
deposit witness: `NewStore`'s first `Unlock` deposited the batch lock's resource), index,
lessor, logger, and the two locks' guards; and what compaction uses: the configuration (a
positive `CompactionBatchLimit`: the job's loop needs it to end,
`issues/etcd-compaction-negative-batch-limit.md`), the scheduler, the stop channel's field (its
channel: `storeStop`; `Close` closes it: `storeCloser`), the hash storage. The fields `restore`
and `Close` change are fixed here (out of scope). `compactMainRev` is under the two locks
(`muInv`, `revMuInv`). -/
def isStore (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (b le : GoInterface) (ti lg : Loc) (Ph : IProp GF) (fh : val) (Dep : IProp GF)
      (scfg : StoreConfig) (ssched : GoInterface) (sstop shs : Loc),
    "#Hb" ∷ s.[store, go!"b"] ↦□ b ∗
    "#Hhook" ∷ hookIs γ Ph fh ∗
    "#Hbk" ∷ isKeyBackendG b (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) Ph fh ∗
    "#Hdep" ∷ □ Dep ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "#Hle" ∷ s.[store, go!"le"] ↦□ le ∗
    "#Hlessor" ∷ isLessor le γ.leases ∗
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "#Hti" ∷ isTreeIndex ti γ.idx ∗
    "#Hlg" ∷ s.[store, go!"lg"] ↦□ lg ∗
    "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
    "#Hmu" ∷ sync.isRWMutexGuard (muAddr s) (muInv s γ) ∗
    "#HrevMu" ∷ sync.isRWMutexGuard (revMuAddr s) (revMuInv s γ) ∗
    "#Hcfg" ∷ s.[store, go!"cfg"] ↦□ scfg ∗
    "%Hcfgl" ∷ ⌜0 < sint.Z scfg.CompactionBatchLimit'⌝ ∗
    "#Hsched" ∷ s.[store, go!"fifoSched"] ↦□ ssched ∗
    "#HisSched" ∷ schedule.isScheduler ssched γ.sch ∗
    "#Hstopc" ∷ s.[store, go!"stopc"] ↦□ sstop ∗
    "#Hhashes" ∷ s.[store, go!"hashes"] ↦□
      (interface.mkOk (go.GoType.PointerType hashStorage.ty) #shs : GoInterface))

/-- **The store's backend contract** (what `NewStore` takes, for every store of the instance):
`isKeyBackendG` at the store's view, tokens and put condition of its instance, its deletable keys
(`delKey`), its lock resource (`storeW`, initially `kbWi`), whether it supports the compaction
(`storeCmp`), the batch lock's invariant `P` and post-lock hook `f`, with some deposit witness. -/
def storeBackend (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF) (f : val) :
    IProp GF :=
  iprop(∃ Dep : IProp GF, isKeyBackendG b (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ)
    (delKey γ) (storeW s γ) (kbWi γ.kb) Dep (storeCmp γ) P f)

instance storeBackend_persistent (b : GoInterface) (s : Loc) (γ : StoreNames) (P : IProp GF)
    (f : val) : Persistent (storeBackend (GF := GF) b s γ P f) := by
  unfold storeBackend; infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance isStore_persistent (s : Loc) (γ : StoreNames) : Persistent (isStore (GF := GF) s γ) := by
  unfold isStore; infer_instance

/-- A transaction's tokens, for a store that may be compacted: a reader slot of each of `s.mu`,
`s.revMu` and the index's lock, and a reader's token of the backend (`storeRT`). -/
def storeReaderC (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ ti : Loc,
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "Hmu" ∷ sync.ownRWMutex (muAddr s) (muInv s γ) ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "Hrt" ∷ storeRT γ)

/-- A transaction's tokens (a reader slot of each of `s.mu`, `s.revMu` and the index's lock, and
a reader's token of the backend), **for a store that is never compacted** (`crevFrozen`): the
readers the transactions' specs take (`store.Read`, `store.Write`; the txn, apply, request path
and watchable store use them). -/
def storeReader (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ ti : Loc,
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "Hmu" ∷ sync.ownRWMutex (muAddr s) (muInv s γ) ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "Hrt" ∷ storeRT γ ∗
    "#Hfrz" ∷ crevFrozen γ)

/-- A reader of a never-compacted store from a reader. -/
theorem storeReader_of (s : Loc) (γ : StoreNames) :
    storeReaderC (GF := GF) s γ ∗ crevFrozen γ ⊢ storeReader s γ := by
  iintro ⟨H, #Hf⟩
  iunfold storeReaderC at H
  icases H with ⟨%ti, H⟩
  iNamed H
  iunfold storeReader
  iexists ti
  iframe Hmu HrevMu Hti Hrt
  iframe #

/-- Readers of a never-compacted store from readers. -/
theorem storeReaders_of (s : Loc) (γ : StoreNames) : ∀ (n : Nat),
    crevFrozen (GF := GF) γ ∗ ([∗list] _x ∈ List.replicate n (), storeReaderC s γ) ⊢
      [∗list] _x ∈ List.replicate n (), storeReader s γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨#Hf, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iapply storeReader_of; iframe H1 Hf
    · iapply storeReaders_of s γ n; iframe Hs Hf

/-- The reader without the frozen fact. -/
theorem storeReader_toC (s : Loc) (γ : StoreNames) :
    storeReader (GF := GF) s γ ⊢ storeReaderC s γ ∗ crevFrozen γ := by
  iintro H
  iunfold storeReader at H
  icases H with ⟨%ti, H⟩
  iNamed H
  iframe Hfrz
  iunfold storeReaderC
  iexists ti
  iframe Hmu HrevMu Hti Hrt
  iframe #

/-! ## The read transaction -/

/-- The `storeTxnRead` of a read transaction at revision `rev` of the committed log `log`
(its fields, read-only): its reader `rt` (as `UnsafeReader` and as `ReadTx`; a snapshot of a
bucket holding `log`'s, `txReader`), `firstRev` is `-1` (the store is never compacted:
`crevFrozen`), `rev` is `log`'s last revision. -/
def storeTxnReadIs (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames) (log : Log)
    (rev : w64) : IProp GF :=
  iprop("#Hs" ∷ (txCommon tr).[storeTxnCommon, go!"s"] ↦□ s ∗
    "#Htxc" ∷ (txCommon tr).[storeTxnCommon, go!"tx"] ↦□ (GoInterface.ok rt : GoInterface) ∗
    "#HfirstRev" ∷ (txCommon tr).[storeTxnCommon, go!"firstRev"] ↦□ (W64 (-1) : w64) ∗
    "#Hrev" ∷ (txCommon tr).[storeTxnCommon, go!"rev"] ↦□ rev ∗
    "#Htrace" ∷ (txCommon tr).[storeTxnCommon, go!"trace"] ↦□ trace ∗
    "#Htx" ∷ tr.[storeTxnRead, go!"tx"] ↦□ (GoInterface.ok rt : GoInterface) ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "%Hrev" ∷ ⌜rev = W64 ((log.length : Int) - 1)⌝ ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "#Hfrz" ∷ crevFrozen γ)

/-- A read transaction's reader `rt`, locked: a snapshot of a bucket holding `log`'s, with the
reader's token (from its `RLock` to the transaction's `End`, which `RUnlock`s it, getting the
store's reader token back). -/
def txReader (γ : StoreNames) (rt : GoInterfaceOk) (log : Log) : IProp GF :=
  iprop(∃ (m : Bucket) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
    "#Hsnap" ∷ keyReadLocked (storeRT γ) false rt m Rd Tok ∗
    "Htok" ∷ Tok ∗
    "%Hsub" ∷ ⌜GMap.Subseteq (bucketMap log) m⌝)

instance storeTxnReadIs_persistent (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames)
    (log : Log) (rev : w64) : Persistent (storeTxnReadIs (GF := GF) tr s rt trace γ log rev) := by
  unfold storeTxnReadIs; infer_instance

/-- The read transaction `store.Read` returns, as the caller sees it: the `metricsTxnWrite`
wrapper at `mw` (its counters), around the `txnReadWrite` wrapper around the `storeTxnRead`,
with the transaction's tokens (`s.mu` held shared until `End`) and its reader's
(`txReader`). -/
def isTxnRead (mw s : Loc) (γ : StoreNames) (log : Log) (rev : w64) : IProp GF :=
  iprop(∃ (trw tr trace ti : Loc) (rt : GoInterfaceOk) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw,
        ranges' := ranges, puts' := W64 0, deletes' := W64 0, putSize' := W64 0 } : metricsTxnWrite) ∗
    "Htrw" ∷ trw.[txnReadWrite, go!"TxnRead"] ↦
      (interface.mkOk (go.GoType.PointerType storeTxnRead.ty) #tr : GoInterface) ∗
    "#Hs" ∷ isStore s γ ∗
    "#Htr" ∷ storeTxnReadIs tr s rt trace γ log rev ∗
    "Hrd" ∷ txReader γ rt log ∗
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "Hmu" ∷ muHeld s γ (-1) ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx)

/-- The store's `readView` (`kv_view.go`): its `kv` is the store `s`. -/
def isReadView (rv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop("#Hkv" ∷ rv.[readView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType store.ty) #s : GoInterface) ∗
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
    (answers : List (GoString × Rev × Rev × w64)) : IProp GF :=
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

/-! ## The write transaction -/

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
transaction locked with the pending puts, the batch lock's resource (`writerRes`, with the
pending changes in the index writer's handle), the revision token the transaction was opened
with, and the transaction's tokens. -/
def storeTxnWriteIs (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(∃ (trace ti : Loc) (bt : GoInterfaceOk) (Locked : Puts → IProp GF) (chs : GoSlice)
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
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "#Hhook" ∷ hookIs γ Pw fw ∗
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw fw ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "Hrt" ∷ storeRT γ ∗
    "Hlocked" ∷ Locked (pendPuts ilog pend) ∗
    "Hw" ∷ idxWriter γ.idx ilog pend ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap ilog) ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hmu" ∷ muHeld s γ (-1) ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "Hcres" ∷ compactRes γ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "#Hfrz" ∷ crevFrozen γ)

/-- The write transaction of `storeTxnWriteIs` without its `changes` slice's contents and their
key-values (`chs ↦* ps`, `changesAre ps ilog pend`: the caller's, `storeTxnWrite.Changes`):
the slice is `chs`, of `ps.length = pend.length` pointers, and the index writer may be sealed
(`idxWriterB`: the watchable store seals the pending revision before it notifies). What
`storeTxnWrite.End` needs (it reads the slice's length only). -/
def storeTxnWriteCore (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) : IProp GF :=
  iprop(∃ (trace ti : Loc) (bt : GoInterfaceOk) (Locked : Puts → IProp GF) (ntok : Nat)
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
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "#Hhook" ∷ hookIs γ Pw fw ∗
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw fw ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "Hrt" ∷ storeRT γ ∗
    "Hlocked" ∷ Locked (pendPuts ilog pend) ∗
    "Hw" ∷ idxWriterB γ.idx ilog pend sealed ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap ilog) ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hmu" ∷ muHeld s γ (-1) ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "Hcres" ∷ compactRes γ ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "#Hfrz" ∷ crevFrozen γ)

/-- The write transaction as its core, its `changes` and their key-values. -/
theorem storeTxnWriteIs_split (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change) :
    storeTxnWriteIs (GF := GF) tw s γ ilog pend ⊢
      ∃ (chs : GoSlice) (ps : List Loc), storeTxnWriteCore tw s γ ilog pend chs ps false ∗
        chs ↦* ps ∗ changesAre ps ilog pend := by
  iintro Htw
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
  iexists chs, ps
  iframe Hchs Hkvs
  iunfold storeTxnWriteCore
  iexists trace, ti, bt, Locked, ntok, Pw, fw, Dep
  simp only [named, idxWriterB_false]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, ⟨Hps, Hlen.1, Hlen.2⟩, Hne, Htrnn⟩

theorem storeTxnWriteIs_join (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) :
    storeTxnWriteCore (GF := GF) tw s γ ilog pend chs ps false ∗ chs ↦* ps ∗
      changesAre ps ilog pend ⊢ storeTxnWriteIs tw s γ ilog pend := by
  iintro ⟨Hc, Hchs, Hkvs⟩
  iunfold storeTxnWriteCore at Hc
  iNamed Hc
  simp only [idxWriterB_false]
  iunfold storeTxnWriteIs
  iexists trace, ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
  simp only [named]
  iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps.1, Hne, Htrnn⟩

/-- **Seal** the write transaction's pending revision (not empty): its history's lower bound
with the revision committed, persistent. -/
theorem storeTxnWriteCore_seal (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (hne : pend ≠ []) :
    storeTxnWriteCore (GF := GF) tw s γ ilog pend chs ps false ==∗
      storeTxnWriteCore tw s γ ilog pend chs ps true ∗
        monoListLbOwn γ.idx.hist (histOf (ilog ++ [pend])) := by
  iintro Hc
  iunfold storeTxnWriteCore at Hc
  iNamed Hc
  simp only [idxWriterB_false]
  imod idxWriter_seal γ.idx ilog pend hne $$ Hw with ⟨Hw, #Hlb⟩
  imodintro
  iframe Hlb
  iunfold storeTxnWriteCore
  iexists trace, ti, bt, Locked, ntok, Pw, fw, Dep
  simp only [named, idxWriterB_true]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩

/-- The write transaction's facts: the writer's log is well formed, and its committed log is
the store's view of `currentRev` (kept). -/
theorem storeTxnWriteCore_wf (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (b : Bool) :
    storeTxnWriteCore (GF := GF) tw s γ ilog pend chs ps b ⊢
      storeTxnWriteCore tw s γ ilog pend chs ps b ∗
        ⌜IdxWf ilog pend ∧ ps.length = pend.length ∧ ps.length = sint.nat chs.len ∧
          0 ≤ sint.Z chs.len ∧ ilog ≠ []⌝ := by
  iintro Hc
  iunfold storeTxnWriteCore at Hc
  iNamed Hc
  ihave %Hwf := idxWriterB_wf γ.idx ilog pend b $$ Hw
  isplitl
  · iunfold storeTxnWriteCore
    iexists trace, ti, bt, Locked, ntok, Pw, fw, Dep
    simp only [named]
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩
  ipureintro; exact ⟨Hwf, Hps.1, Hps.2.1, Hps.2.2, Hne⟩

/-- The write transaction `store.Write` returns, as the caller sees it: the `metricsTxnWrite`
wrapper at `mw` (its counters `puts`, `deletes`, `putSize`) around the `storeTxnWrite`. -/
def isTxnWrite (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) : IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteIs tw s γ ilog pend)

/-- The write transaction at `mw` without its key-values (`storeTxnWriteCore`). -/
def isTxnWriteCore (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (sealed : Bool) : IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteCore tw s γ ilog pend chs ps sealed)

theorem isTxnWrite_split (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) :
    isTxnWrite (GF := GF) mw s γ ilog pend puts deletes putSize ⊢
      ∃ (chs : GoSlice) (ps : List Loc),
        isTxnWriteCore mw s γ ilog pend puts deletes putSize chs ps false ∗
        chs ↦* ps ∗ changesAre ps ilog pend := by
  iintro H
  iunfold isTxnWrite at H
  iNamed H
  icases storeTxnWriteIs_split tw s γ ilog pend $$ Htw with ⟨%chs, %ps, Hc, Hchs, Hkvs⟩
  iexists chs, ps
  iframe Hchs Hkvs
  iunfold isTxnWriteCore
  iexists tw, ranges
  iframe

theorem isTxnWrite_join (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) :
    isTxnWriteCore (GF := GF) mw s γ ilog pend puts deletes putSize chs ps false ∗
      chs ↦* ps ∗ changesAre ps ilog pend ⊢ isTxnWrite mw s γ ilog pend puts deletes putSize := by
  iintro ⟨H, Hchs, Hkvs⟩
  iunfold isTxnWriteCore at H
  iNamed H
  iunfold isTxnWrite
  iexists tw, ranges
  iframe Hmw
  iapply storeTxnWriteIs_join $$ [$Htw $Hchs $Hkvs]

theorem isTxnWriteCore_seal (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (hne : pend ≠ []) :
    isTxnWriteCore (GF := GF) mw s γ ilog pend puts deletes putSize chs ps false ==∗
      isTxnWriteCore mw s γ ilog pend puts deletes putSize chs ps true ∗
        monoListLbOwn γ.idx.hist (histOf (ilog ++ [pend])) := by
  iintro H
  iunfold isTxnWriteCore at H
  iNamed H
  imod storeTxnWriteCore_seal tw s γ ilog pend chs ps hne $$ Htw with ⟨Htw, #Hlb⟩
  imodintro
  iframe Hlb
  iunfold isTxnWriteCore
  iexists tw, ranges
  iframe

/-- The log a write transaction commits at `End`: the pending revision appended, if it has a
change (else no revision is made). -/
def commitLog (ilog : Log) (pend : List Change) : Log :=
  if pend = [] then ilog else ilog ++ [pend]

/-- The transaction's revision is the last of the log it would commit. -/
theorem writeRev_commitLog (ilog : Log) (pend : List Change) :
    writeRev ilog pend = (commitLog ilog pend).length - 1 := by
  unfold writeRev commitLog; split <;> simp

/-- A transaction behind a `metricsTxnWrite`: a read transaction, or a write transaction. -/
inductive TxnKind where
  | read (log : Log) (rev : w64)
  | write (ilog : Log) (pend : List Change) (puts deletes putSize : w64)

def isTxn (mw s : Loc) (γ : StoreNames) : TxnKind → IProp GF
  | .read log rev => isTxnRead mw s γ log rev
  | .write ilog pend puts deletes putSize => isTxnWrite mw s γ ilog pend puts deletes putSize

/-- What `End` needs of a transaction (`metricsTxnWrite.End`): a read transaction; a write
transaction's core (its key-values released: `isTxnWrite_split`), sealed or not. -/
def isTxnEnd (mw s : Loc) (γ : StoreNames) : TxnKind → IProp GF
  | .read log rev => isTxnRead mw s γ log rev
  | .write ilog pend puts deletes putSize =>
    iprop(∃ (chs : GoSlice) (ps : List Loc) (sealed : Bool),
      isTxnWriteCore mw s γ ilog pend puts deletes putSize chs ps sealed)

/-- A transaction is ready to end (its key-values, if any, dropped). -/
theorem isTxn_toEnd (mw s : Loc) (γ : StoreNames) (kind : TxnKind) :
    isTxn (GF := GF) mw s γ kind ⊢ isTxnEnd mw s γ kind := by
  cases kind with
  | read log rev => exact .rfl
  | write ilog pend puts deletes putSize =>
    simp only [isTxn, isTxnEnd]
    iintro H
    icases isTxnWrite_split mw s γ ilog pend puts deletes putSize $$ H with ⟨%chs, %ps, Hc, -, -⟩
    iexists chs, ps, false
    iexact Hc

/-- What `End` leaves of a transaction: nothing of a read one; of a write one, the
certificate of the committed log, and the revision token back if no revision was made. -/
def txnEndPost (γ : StoreNames) : TxnKind → IProp GF
  | .read _ _ => iprop(True)
  | .write ilog pend _ _ _ =>
    iprop(idxCert γ.idx (commitLog ilog pend) ∗ if pend = [] then revToken γ else iprop(True))

/-- What `End` takes of a transaction: nothing of a read one; of a write one, the batch lock's
invariant `P` (the store's: `hookIs`), which `Unlock` takes back. -/
def txnEndPre (γ : StoreNames) : TxnKind → IProp GF
  | .read _ _ => iprop(True)
  | .write _ _ _ _ _ => iprop(∃ (P : IProp GF) (f : val), hookIs γ P f ∗ P)

theorem txnEndPre_write (γ : StoreNames) (P : IProp GF) (f : val) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) :
    hookIs γ P f ∗ P ⊢ txnEndPre γ (.write ilog pend puts deletes putSize) := by
  iintro ⟨#Hh, HP⟩
  simp only [txnEndPre]
  iexists P, f
  iframe Hh HP

/-- The store's `writeView` (`kv_view.go`): its `kv` is the store `s`. -/
def isWriteView (wv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop("#Hkv" ∷ wv.[writeView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType store.ty) #s : GoInterface) ∗
    "#Hs" ∷ isStore s γ)

instance isWriteView_persistent (wv s : Loc) (γ : StoreNames) :
    Persistent (isWriteView (GF := GF) wv s γ) := by
  unfold isWriteView; infer_instance


end reprs

section hookLc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- Two views of the hook agree, the invariants now (a later credit spent): the same function,
each invariant gives the other. -/
theorem hookIs_agree_lc (E : CoPset) (γ : StoreNames) (P P' : IProp GF) (f f' : val) :
    £ 1 ∗ hookIs γ P f ∗ hookIs γ P' f' ⊢
      |={E}=> ⌜f = f'⌝ ∗ □ (P -∗ P') ∗ □ (P' -∗ P) := by
  iintro ⟨Hlc, #H1, #H2⟩
  ihave ⟨%Hf, Heq⟩ := hookIs_agree γ P P' f f' $$ [H1 H2]
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

/-- The store's stop channel (persistent; `NewStore` returns it): its `stopc` field and the
channel (the compaction job's loop selects on it). -/
def storeStop (s : Loc) : IProp GF :=
  iprop(∃ c : GoChan, s.[store, go!"stopc"] ↦□ c ∗ isStopChan c)

instance storeStop_persistent (s : Loc) : Persistent (storeStop (GF := GF) s) := by
  unfold storeStop; infer_instance

/-- The right to close the store (`store.Close`, which closes its `stopc`: once): the stop
channel's close (`stopCloser`; `NewStore` returns it). -/
def storeCloser (s : Loc) : IProp GF :=
  iprop(∃ c : GoChan, s.[store, go!"stopc"] ↦□ c ∗ stopCloser c)

end hookLc

end mvcc
end EtcdGrove
end Perennial
