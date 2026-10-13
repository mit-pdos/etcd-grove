/-
The store (`kvstore.go`, `kvstore_txn.go`): the backend's contract for the `Key` bucket (the
trust boundary of bbolt and the read buffer), the store's locks and what they hold, and the read
transaction. Lean-first; `notes/decisions.md`, "The transactions: the store's locks and the
backend contract".

**The backend.** `keyReadSnap View RT rt m` says `rt` is a `ReadTx` over a snapshot `m` of the
bucket (its `RLock` gives a token under which `UnsafeRange(schema.Key, k, nil, 0)` returns `k`'s
entry of `m`, or nothing: `keyReadLocked`); `isKeyBackend b View` that `b`'s
`ConcurrentReadTx()`/`ReadTx()` return one of the bucket the caller's `View q m` holds (the
store's ghost map authority at the caller's fraction). `isKeyBackendG` is the general contract,
with the backend's tokens and conditions (`BackendBridge.lean` proves it of the backend);
`isKeyBackend`, the store's, its instance without them.

**The locks.** `s.mu` (every transaction holds it shared; exclusively only by what is out of
scope) holds nothing. `s.revMu` holds `currentRev` (the committed log's last revision),
`compactMainRev` (`-1`, no compaction), the index's certificate of the committed log and the
bucket's authority: a reader's snapshot, taken under it, is the committed log's bucket. It also
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
  /-- a ghost map of the granted leases (persistent elements): what `Attach` needs -/
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

instance idxNames_countable : Pos.Countable IdxNames :=
  countableOfLeftInverse (fun x : IdxNames => (x.hist, x.nev, x.log))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

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
    (fun x : StoreNames => (x.idx, x.bucket, x.clog, x.leases, x.revs, x.hook, x.hookFn, x.kb))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

set_option linter.unusedVariables false in
/-- `s.mu`'s resource: nothing (see the module docstring); it takes the semantics' instances
(unused) so that the lock lemmas' own are determined at its uses. -/
def muInv [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    [sem : go.Semantics] (_q : Qp) : IProp GF := iprop(True)

instance muInv_fractional [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] [sem : go.Semantics] : Fractional (muInv (hG := hG)) where
  fractional _ _ := by
    unfold muInv
    constructor
    · iintro _; isplitl [] <;> itrivial
    · iintro _; itrivial

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
the shared transaction's state is the one at its `RLock`, not at `ReadTx()`). -/
def keyReadSnap (View : Qp → Bucket → IProp GF) (RT : IProp GF) (rng : Bool) (rt : GoInterfaceOk)
    (m : Bucket) (L : IProp GF) : IProp GF :=
  iprop(□ (∀ q : Qp, {{ L ∗ View q m }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
    {{ RET #(); View q m ∗ ∃ (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF), Tok ∗
        keyReadLocked RT rng rt m Rd Tok }}))

instance keyReadSnap_persistent (View : Qp → Bucket → IProp GF) (RT : IProp GF) (rng : Bool)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    Persistent (keyReadSnap View RT rng rt m L) := by
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
backend's `batchLocked` at the session's state, whose bbolt transaction the slices are of).

The store's instance (`batchTxSpec`) has no tokens (`RT = WT = True`) and no condition: the
backend's bridge (`BackendBridge.lean`) proves it with the backend's (2026-10-13, unit 4). -/
def batchTxSpecG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (W : IProp GF) (Locked : Puts → IProp GF)
    (P : IProp GF) (f : val) : IProp GF :=
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
          keyVals Rd ks vs (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) k }}))

instance batchTxSpecG_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop) (W : IProp GF)
    (Locked : Puts → IProp GF) (P : IProp GF) (f : val) :
    Persistent (batchTxSpecG bt View RT WT PutOk W Locked P f) := by
  unfold batchTxSpecG; infer_instance

/-- `NewStore`'s calls on a fresh backend's batch transaction `bt`, with `LockedO n` the lock's
token after `n` buckets created: `LockOutsideApply()` takes the lock, for a session's token
`WT` (the client's token `RT` lent), with the lock's initial resource `Wi` only (`True` for
mvcc's assumed backend; the real backend's late-bound resource `lateW`, not yet registered,
2026-10-13, unit 5): the backend's batch lock holds `W` from `NewStore`'s first `Unlock()` on
(the triple takes `W` and deposits it there; `NewStore` builds `W` before, from `Wi`);
`LockInsideApply` is the writers' lock, taken after that. `UnsafeCreateBucket(b)`
under the lock, of schema's `Key` or `Meta` bucket, creates it (not touching the `Key` bucket's
entries), at most twice (the backend's bound on a session's operations; `NewStore` creates
two). -/
def batchTxInitSpec (bt : GoInterfaceOk) (RT WT : IProp GF) (W Wi : IProp GF)
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
      {{ RET #(); True }}))

instance batchTxInitSpec_persistent (bt : GoInterfaceOk) (RT WT : IProp GF) (W Wi : IProp GF)
    (LockedO : Nat → IProp GF) (P : IProp GF) :
    Persistent (batchTxInitSpec bt RT WT W Wi LockedO P) := by
  unfold batchTxInitSpec; infer_instance

/-- `bt` is a batch transaction (its lock tokens' predicates are its own). -/
def isBatchTxG (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (W Wi : IProp GF) (P : IProp GF)
    (f : val) : IProp GF :=
  iprop(∃ (Locked : Puts → IProp GF) (LockedO : Nat → IProp GF),
    batchTxSpecG bt View RT WT PutOk W Locked P f ∗ batchTxInitSpec bt RT WT W Wi LockedO P)

instance isBatchTxG_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop) (W Wi : IProp GF)
    (P : IProp GF) (f : val) : Persistent (isBatchTxG bt View RT WT PutOk W Wi P f) := by
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
on the puts. -/
def batchTxSpec (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W : IProp GF)
    (Locked : Puts → IProp GF) (P : IProp GF) (f : val) : IProp GF :=
  batchTxSpecG bt View iprop(True) iprop(True) noPutCond W Locked P f

instance batchTxSpec_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (W : IProp GF) (Locked : Puts → IProp GF) (P : IProp GF) (f : val) :
    Persistent (batchTxSpec bt View W Locked P f) := by
  unfold batchTxSpec; infer_instance

/-- `bt` is a batch transaction (mvcc's assumed backend). -/
def isBatchTx (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W : IProp GF)
    (P : IProp GF) (f : val) : IProp GF :=
  isBatchTxG bt View iprop(True) iprop(True) noPutCond W iprop(True) P f

/-- The batch transaction under its lock is a reader of its own puts over the view. -/
theorem batchTx_reader (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (W : IProp GF)
    (Locked : Puts → IProp GF) (P : IProp GF) (f : val) (l : Puts) (q : Qp) (m : Bucket) :
    batchTxSpecG bt View RT WT PutOk W Locked P f ⊢
      keyReader bt (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) iprop(Locked l ∗ View q m) := by
  iintro #H
  iunfold batchTxSpecG at H
  icases H with ⟨-, -, -, -, #Hr⟩
  iunfold keyReader
  iintro %b %key %k %dq !> %Φ ⟨#HK, ⟨Hl, Hv⟩, Hkey⟩ HΦ
  iapply Hr $$ %l %q %m %b %key %k %dq %Φ [Hl Hv Hkey]
  · iframe Hl Hv Hkey; iexact HK
  inext
  iintro %ks %vs ⟨%Rd, %T, HT, Hback, #Hcap, Hv, Hkey, #Hkv⟩
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
theorem batchTxSpec_reader (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W : IProp GF)
    (Locked : Puts → IProp GF) (P : IProp GF) (f : val) (l : Puts) (q : Qp) (m : Bucket) :
    batchTxSpec bt View W Locked P f ⊢
      keyReader bt (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) iprop(Locked l ∗ View q m) := by
  unfold batchTxSpec
  exact batchTx_reader bt View _ _ _ W Locked P f l q m

instance isBatchTx_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (W : IProp GF) (P : IProp GF) (f : val) : Persistent (isBatchTx bt View W P f) := by
  unfold isBatchTx; infer_instance

/-- `b` is a `Backend` whose `ConcurrentReadTx()` and `ReadTx()`, for a reader's token `RT`
(the backend's readers are bounded: a slot of its read lock and of its `txMu`, a budget token,
and the backend open; given back by the reader's `RUnlock`), return a snapshot reader of the
bucket the caller holds as `View q m` (any fraction `q`), which the caller keeps, with the right
`L` to lock it (`keyReadSnap`: its `RLock` gives the reader's token, its `RUnlock` takes it),
and whose `BatchTx()` is a batch transaction over the view, its lock holding `W`;
`ForceCommit()`, for a session's token `WT` (`RT` lent), returns (the commit to disk has no
effect on the view). The store's instance (`isKeyBackend`) has no tokens and no condition on
the puts (`batchTxSpecG`'s `PutOk`); `BackendBridge.lean` proves the general one of the
backend (2026-10-13, unit 4). -/
def isKeyBackendG (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (W Wi : IProp GF) (P : IProp GF)
    (f : val) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnap View RT false rt m L }}) ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m ∗ RT }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗
          ∃ L : IProp GF, L ∗ keyReadSnap View RT true rt m L }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt);
          isBatchTxG bt View RT WT PutOk W Wi P f }}) ∗
    □ ({{ RT ∗ WT }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      {{ RET #(); RT }}))

instance isKeyBackendG_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop) (W Wi : IProp GF)
    (P : IProp GF) (f : val) : Persistent (isKeyBackendG b View RT WT PutOk W Wi P f) := by
  unfold isKeyBackendG; infer_instance

/-- mvcc's assumed backend contract: no tokens, no condition on the puts, nothing in the lock
before `NewStore`'s first `Unlock`. -/
def isKeyBackend (b : GoInterface) (View : Qp → Bucket → IProp GF) (W : IProp GF)
    (P : IProp GF) (f : val) : IProp GF :=
  isKeyBackendG b View iprop(True) iprop(True) noPutCond W iprop(True) P f

instance isKeyBackend_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (W : IProp GF) (P : IProp GF) (f : val) : Persistent (isKeyBackend b View W P f) := by
  unfold isKeyBackend; infer_instance

/-! ## The lessor -/

/-- The lease `id` is one the lessor granted: a persistent ghost fact of the lessor's ghost
map `γl` (the store's `γ.leases`; the lessor's `Grant`, out of scope, allocates it). `Attach`
needs it. -/
def leaseKnown (γl : GName) (id : w64) : IProp GF :=
  iprop(id ↪[γl]□ ())

instance leaseKnown_persistent (γl : GName) (id : w64) : Persistent (leaseKnown (GF := GF) γl id) := by
  unfold leaseKnown; infer_instance

/-- The lessor `le` (`lease.Lessor`, names-only: the trust boundary), as the KV core uses it:
`GetLease(item)` returns some lease id (`NoLease` if none); `Attach(id, items)` of a granted
lease returns `nil`; `Detach(id, items)` returns `nil` or an error (which the code logs). The
items are read. Leases have no liveness here: what the lessor does with them is its own.
`SetRangeDeleter(f)` returns: `NewStore` passes the closure `func() lease.TxnDelete { return
s.Write(traceutil.TODO()) }` (the store's own verified `store.Write`), which the contract takes
as an opaque value; the lessor's later calls of it (on a lease's expiry) are outside the model.
The lessor's ghost name `γl` is its own (it exists before the store). -/
def isLessor (le : GoInterface) (γl : GName) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ (item : go_etcd_io.etcd.server.v3.lease.LeaseItem),
      {{ True }} (App (Val #(methods li.ty go!"GetLease" li.v)) (Val #item))
      {{ (id : w64), RET #id; True }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac),
      {{ leaseKnown γl id ∗ items ↦*{dq} l }}
        (App (App (Val #(methods li.ty go!"Attach" li.v)) (Val #id)) (Val #items))
      {{ RET #(GoInterface.nil); items ↦*{dq} l }}) ∗
    □ (∀ (id : w64) (items : GoSlice) (l : List go_etcd_io.etcd.server.v3.lease.LeaseItem)
        (dq : DFrac),
      {{ items ↦*{dq} l }}
        (App (App (Val #(methods li.ty go!"Detach" li.v)) (Val #id)) (Val #items))
      {{ (err : GoInterface), RET #err; items ↦*{dq} l }}) ∗
    □ (∀ f : val,
      {{ True }} (App (Val #(methods li.ty go!"SetRangeDeleter" li.v)) (Val f))
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

/-! ## The locks -/


/-- The batch lock's resource for the store (`W` of `isKeyBackend`): the index writer's handle
at the committed log `ilog` with no pending change, half the committed-log ghost variable (the
other half under `s.revMu`), half of `currentRev` (`store.Write` reads it under the batch lock
alone), half the bucket's view (the other half under `s.revMu`: the write transaction's reads
of the bucket, through the batch transaction), the certificate of `ilog`, and half the
revision budget's authority (the other half under `s.revMu`). -/
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
    "%Hne" ∷ ⌜ilog ≠ []⌝)

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

/-- `s.revMu`'s resource at fraction `q`: the committed log `log`'s last revision in
`currentRev` (half of it: the writer holds the other half under the batch lock), half the
committed-log ghost variable, the index's certificate of `log` and the bucket's authority
(`bucketMap log`, half of it: the batch lock holds the other half), half the revision
budget's authority with its bound for `log`, and half the committed log's authority (the index
writer holds the other half). (`compactMainRev` is fixed at `-1`, no compaction in scope:
`isStore`; `rangeKeys` reads it without the lock.) -/
def revMuInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ (log : Log) (ntok : Nat),
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketView γ q.half (bucketMap log) ∗
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own q.half) ntok ∗
    "%Hbudget" ∷ ⌜log.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hlog" ∷ idxLogAuth γ.idx q.half log)

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
    unfold revMuInv
    rw [qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro H
      icases H with ⟨%log, %ntok, H⟩
      iNamed H
      icases (hcur _).1 $$ Hrev with ⟨Hr1, Hr2⟩
      icases (hclog log).1 $$ Hclog with ⟨Hc1, Hc2⟩
      icases (hbv _).1 $$ Hbucket with ⟨Hb1, Hb2⟩
      icases (htk ntok).1 $$ Htoks with ⟨Ht1, Ht2⟩
      icases (hlg log).1 $$ Hlog with ⟨Hl1, Hl2⟩
      isplitl [Hr1 Hc1 Hb1 Ht1 Hl1]
      · iexists log, ntok; simp only [named]; iframe Hr1 Hc1 Hb1 Ht1 Hl1; iframe #; ipureintro
        exact ⟨Hne, Hbudget⟩
      · iexists log, ntok; simp only [named]; iframe Hr2 Hc2 Hb2 Ht2 Hl2; iframe #; ipureintro
        exact ⟨Hne, Hbudget⟩
    · iintro ⟨H1, H2⟩
      icases H1 with ⟨%log, %ntok, H1⟩
      icases H2 with ⟨%log2, %ntok2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      ihave %Hlog := ghostVar_agree γ.clog _ _ _ _ $$ Hclog1 Hclog2
      subst Hlog
      icombine Htoks1 Htoks2 gives %Hn
      obtain ⟨-, Hn⟩ := Hn
      subst Hn
      iexists log, ntok
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
      iapply (hlg log).2; iframe Hlog1 Hlog2

/-- A store (persistent): its backend, index, lessor, logger, and the two locks' guards. The
fields `restore` and `Close` change are fixed here (out of scope). -/
def isStore (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (b le : GoInterface) (ti lg : Loc) (Ph : IProp GF) (fh : val),
    "#Hb" ∷ s.[store, go!"b"] ↦□ b ∗
    "#Hhook" ∷ hookIs γ Ph fh ∗
    "#Hbk" ∷ isKeyBackendG b (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (storeW s γ)
      (kbWi γ.kb) Ph fh ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "#Hle" ∷ s.[store, go!"le"] ↦□ le ∗
    "#Hlessor" ∷ isLessor le γ.leases ∗
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "#Hti" ∷ isTreeIndex ti γ.idx ∗
    "#Hlg" ∷ s.[store, go!"lg"] ↦□ lg ∗
    "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
    "#Hcmp" ∷ s.[store, go!"compactMainRev"] ↦□ (W64 (-1) : w64) ∗
    "#Hmu" ∷ sync.isRWMutexGuard (muAddr s) muInv ∗
    "#HrevMu" ∷ sync.isRWMutexGuard (revMuAddr s) (revMuInv s γ))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance isStore_persistent (s : Loc) (γ : StoreNames) : Persistent (isStore (GF := GF) s γ) := by
  unfold isStore; infer_instance

/-- A transaction's tokens: a reader slot of each of `s.mu`, `s.revMu` and the index's lock, and
a reader's token of the backend (`storeRT`). -/
def storeReader (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ ti : Loc,
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "Hmu" ∷ sync.ownRWMutex (muAddr s) muInv ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "Hrt" ∷ storeRT γ)

/-- The right to close the store (`store.Close`, which closes its `stopc`: once): the `stopc`
field, owned (`NewStore` returns it; nothing else writes it). -/
def storeCloser (s : Loc) : IProp GF := iprop(∃ c : GoChan, s.[store, go!"stopc"] ↦ c)

/-! ## The read transaction -/

/-- The `storeTxnRead` of a read transaction at revision `rev` of the committed log `log`
(its fields, read-only): its reader `rt` (as `UnsafeReader` and as `ReadTx`; a snapshot of a
bucket holding `log`'s, `txReader`), `firstRev` is `-1`, `rev` is `log`'s last revision. -/
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
    "%Htrnn" ∷ ⌜trace ≠ null⌝)

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
    "Hmu" ∷ sync.ownRWMutexRLocked (muAddr s) muInv ∗
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
    (ps : List Loc) (ntok : Nat) (Pw : IProp GF) (fw : val),
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
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (storeW s γ)
      Locked Pw fw ∗
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
    "Hmu" ∷ sync.ownRWMutexRLocked (muAddr s) muInv ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝)

/-- The write transaction of `storeTxnWriteIs` without its `changes` slice's contents and their
key-values (`chs ↦* ps`, `changesAre ps ilog pend`: the caller's, `storeTxnWrite.Changes`):
the slice is `chs`, of `ps.length = pend.length` pointers, and the index writer may be sealed
(`idxWriterB`: the watchable store seals the pending revision before it notifies). What
`storeTxnWrite.End` needs (it reads the slice's length only). -/
def storeTxnWriteCore (tw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) : IProp GF :=
  iprop(∃ (trace ti : Loc) (bt : GoInterfaceOk) (Locked : Puts → IProp GF) (ntok : Nat)
    (Pw : IProp GF) (fw : val),
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
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (storeW s γ)
      Locked Pw fw ∗
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
    "Hmu" ∷ sync.ownRWMutexRLocked (muAddr s) muInv ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝)

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
  iexists trace, ti, bt, Locked, ntok, Pw, fw
  simp only [named, idxWriterB_false]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt
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
  iexists trace, ti, bt, Locked, chs, ps, ntok, Pw, fw
  simp only [named]
  iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt
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
  iexists trace, ti, bt, Locked, ntok, Pw, fw
  simp only [named, idxWriterB_true]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt
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
    iexists trace, ti, bt, Locked, ntok, Pw, fw
    simp only [named]
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt
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

end hookLc

end mvcc
end EtcdGrove
end Perennial
