/-
The store (`kvstore.go`, `kvstore_txn.go`): the backend's contract for the `Key` bucket (the
trust boundary of bbolt and the read buffer), the store's locks and what they hold, and the read
transaction. Lean-first; `notes/decisions.md`, "The transactions: the store's locks and the
backend contract".

**The backend.** `keyReadSnap rt m` says `rt` is a `ReadTx` over a snapshot `m` of the bucket
(`UnsafeRange(schema.Key, k, nil, 0)` returns `k`'s entry of `m`, read-only, or nothing);
`isKeyBackend b View` that `b`'s `ConcurrentReadTx()`/`ReadTx()` return one of the bucket the
caller's `View q m` holds (the store's ghost map authority at the caller's fraction).

**The locks.** `s.mu` (every transaction holds it shared; exclusively only by what is out of
scope) holds nothing. `s.revMu` holds `currentRev` (the committed log's last revision),
`compactMainRev` (`-1`, no compaction), the index's certificate of the committed log and the
bucket's authority: a reader's snapshot, taken under it, is the committed log's bucket.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Perennial.Ghost.GhostVar
public import Perennial.Proof.TokSet
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- The `Key` bucket's written-back contents: a revision's bytes to the encoded key-value. -/
abbrev Bucket := GMap GoString GoString

/-- The ghost names of a store: its index's and its bucket's. -/
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

/-! ### Countability of the log (for its ghost variable) -/

def Change.enc : Change → Bool × GoString × GoString × w64
  | .put k v l => (false, k, v, l)
  | .del k => (true, k, [], W64 0)

theorem Change.enc_inj : Function.Injective Change.enc := by
  intro x y h
  cases x <;> cases y <;> simp only [Change.enc, Prod.mk.injEq] at h
  · obtain ⟨-, rfl, rfl, rfl⟩ := h; rfl
  · exact Bool.noConfusion h.1
  · exact Bool.noConfusion h.1
  · obtain ⟨-, rfl, -, -⟩ := h; rfl

instance Change.countable : Pos.Countable Change :=
  .ofInjective (fun c => Pos.Countable.encode c.enc) (fun _ _ h => Change.enc_inj (Pos.encode_inj h))

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

/-- What `UnsafeRange(Key, k, nil, 0)` returns of the bucket `m`: the key and its value if `m`
has `k` (read-only slices), else no key and no value. -/
def keyVals (ks vs : GoSlice) (m : Bucket) (k : GoString) : IProp GF :=
  match m.lookup k with
  | some v => iprop(∃ (ksl vsl : GoSlice), ks ↦*□ [ksl] ∗ ksl ↦*□ k ∗ vs ↦*□ [vsl] ∗ vsl ↦*□ v)
  | none => iprop(ks ↦*□ ([] : List GoSlice) ∗ vs ↦*□ ([] : List GoSlice))

instance keyVals_persistent (ks vs : GoSlice) (m : Bucket) (k : GoString) :
    Persistent (keyVals (GF := GF) ks vs m k) := by
  unfold keyVals; split <;> infer_instance

/-- `rt`'s `UnsafeRange(schema.Key, key, nil, 0)`, for `key` holding `k`, reads `k`'s entry of
the snapshot `m`. -/
def keyRangeSpec (rt : GoInterfaceOk) (m : Bucket) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ key ↦*{dq} k }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); key ↦*{dq} k ∗ keyVals ks vs m k }})

/-- `rt` is a `ReadTx` over the snapshot `m` of the bucket (persistent): `RLock`/`RUnlock`
return, and its reads are the snapshot's. -/
def keyReadSnap (rt : GoInterfaceOk) (m : Bucket) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    □ keyRangeSpec rt m)

instance keyReadSnap_persistent (rt : GoInterfaceOk) (m : Bucket) :
    Persistent (keyReadSnap (GF := GF) rt m) := by
  unfold keyReadSnap; infer_instance

/-- A reader of the bucket `m` through `rt` (what `rangeKeys` needs of its `tx`): `rt`'s
`UnsafeRange(schema.Key, key, nil, 0)`, for `key` holding `k`, reads `k`'s entry of `m`, with
the owned resource `R` it needs (nothing for a read transaction's snapshot; the batch
transaction's lock token and the bucket's view for a write transaction's). -/
def keyReader (rt : GoInterfaceOk) (m : Bucket) (R : IProp GF) : IProp GF :=
  iprop(∀ (b : GoInterface) (key : GoSlice) (k : GoString) (dq : DFrac),
    {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ R ∗ key ↦*{dq} k }}
      (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); R ∗ key ↦*{dq} k ∗ keyVals ks vs m k }})

instance keyReader_persistent (rt : GoInterfaceOk) (m : Bucket) (R : IProp GF) :
    Persistent (keyReader (GF := GF) rt m R) := by
  unfold keyReader; infer_instance

/-- A snapshot is a reader, with nothing owned. -/
theorem keyReadSnap_reader (rt : GoInterfaceOk) (m : Bucket) :
    keyReadSnap (GF := GF) rt m ⊢ keyReader rt m iprop(True) := by
  iintro #H
  iunfold keyReadSnap at H
  icases H with ⟨-, -, #Hr⟩
  iunfold keyRangeSpec at Hr
  iunfold keyReader
  iintro %b %key %k %dq !> %Φ ⟨#HK, -, Hkey⟩ HΦ
  iapply Hr $$ %b %key %k %dq %Φ [Hkey]
  · iframe Hkey; iexact HK
  inext
  iintro %ks %vs ⟨Hkey, #Hkv⟩
  iapply HΦ
  iframe Hkey Hkv

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
    icases H with ⟨-, -, %Hc⟩
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

/-! ## The batch transaction -/

/-- The entries a batch transaction has put into the `Key` bucket since it was locked, in
order (`UnsafeSeqPut`). -/
abbrev Puts := List (GoString × GoString)

/-- The batch transaction `bt` (`backend.BatchTx`, names-only: the trust boundary of the
backend's write path), as the write transaction uses it, with `Locked l` its lock's token
holding the puts `l` since the lock was taken: `LockInsideApply()` takes the lock (no puts
yet) and gives the lock's resource `W` (what the store keeps under it); `UnsafeSeqPut(
schema.Key, k, v)` under it adds a put; `Unlock()` takes the resource back and, with no puts,
leaves the bucket as it is, else writes the puts back into the bucket, whose view `View 1 m`
the caller holds (`storeTxnWrite.End` holds it, half under `s.revMu`, half in `W`), in order,
then releases the lock with `W` made of the updated view (a wand: `W` holds part of the view);
`UnsafeRange(schema.Key, k, nil, 0)` under the lock reads the bucket the caller holds a view
of with the puts so far (the batch transaction sees its own puts).

`NewStore`'s calls on a fresh backend: `LockOutsideApply()` takes the lock with no puts and
*no* resource: the backend's batch lock holds `W` from `NewStore`'s first `Unlock()` on (the
no-puts `Unlock` triple, which takes `W`, deposits it there; `NewStore` builds `W` before);
`LockInsideApply` is the writers' lock, taken after that. `UnsafeCreateBucket(b)` under the
lock leaves the puts as they are (it does not touch the `Key` bucket's entries). -/
def batchTxSpec (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W : IProp GF)
    (Locked : Puts → IProp GF) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods bt.ty go!"LockInsideApply" bt.v)) (Val #()))
      {{ RET #(); Locked [] ∗ W }}) ∗
    □ (∀ (l : Puts) (b : GoInterface) (key val : GoSlice) (k v : GoString) (dq dq' : DFrac),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked l ∗
          key ↦*{dq} k ∗ val ↦*{dq'} v }}
        (App (App (App (Val #(methods bt.ty go!"UnsafeSeqPut" bt.v)) (Val #b)) (Val #key))
          (Val #val))
      {{ RET #(); Locked (l ++ [(k, v)]) ∗ key ↦*{dq} k ∗ val ↦*{dq'} v }}) ∗
    □ ({{ Locked [] ∗ W }} (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); True }}) ∗
    □ (∀ (l : Puts) (m : Bucket) (Q : IProp GF),
      {{ Locked l ∗ View 1 m ∗ (View 1 (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) -∗ W ∗ Q) }}
        (App (Val #(methods bt.ty go!"Unlock" bt.v)) (Val #()))
      {{ RET #(); Q }}) ∗
    □ (∀ (l : Puts) (q : Qp) (m : Bucket) (b : GoInterface) (key : GoSlice) (k : GoString)
        (dq : DFrac),
      {{ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Key ↦□ b ∗ Locked l ∗ View q m ∗
          key ↦*{dq} k }}
        (App (App (App (App (Val #(methods bt.ty go!"UnsafeRange" bt.v)) (Val #b)) (Val #key))
          (Val #(slice.nil))) (Val #(W64 0)))
      {{ (ks vs : GoSlice), RET (PairV #ks #vs); Locked l ∗ View q m ∗ key ↦*{dq} k ∗
          keyVals ks vs (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) k }}) ∗
    □ ({{ True }} (App (Val #(methods bt.ty go!"LockOutsideApply" bt.v)) (Val #()))
      {{ RET #(); Locked [] }}) ∗
    □ (∀ (l : Puts) (b : GoInterface),
      {{ Locked l }} (App (Val #(methods bt.ty go!"UnsafeCreateBucket" bt.v)) (Val #b))
      {{ RET #(); Locked l }}))

instance batchTxSpec_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (W : IProp GF) (Locked : Puts → IProp GF) : Persistent (batchTxSpec bt View W Locked) := by
  unfold batchTxSpec; infer_instance

/-- `bt` is a batch transaction (its lock token's predicate is its own). -/
def isBatchTx (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W : IProp GF) : IProp GF :=
  iprop(∃ Locked : Puts → IProp GF, batchTxSpec bt View W Locked)

/-- The batch transaction under its lock is a reader of its own puts over the view. -/
theorem batchTx_reader (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (W : IProp GF)
    (Locked : Puts → IProp GF) (l : Puts) (q : Qp) (m : Bucket) :
    batchTxSpec bt View W Locked ⊢
      keyReader bt (l.foldl (fun m p => GMap.insert p.1 p.2 m) m) iprop(Locked l ∗ View q m) := by
  iintro #H
  iunfold batchTxSpec at H
  icases H with ⟨-, -, -, -, #Hr, -⟩
  iunfold keyReader
  iintro %b %key %k %dq !> %Φ ⟨#HK, ⟨Hl, Hv⟩, Hkey⟩ HΦ
  iapply Hr $$ %l %q %m %b %key %k %dq %Φ [Hl Hv Hkey]
  · iframe Hl Hv Hkey; iexact HK
  inext
  iintro %ks %vs ⟨Hl, Hv, Hkey, #Hkv⟩
  iapply HΦ
  iframe Hl Hv Hkey Hkv

instance isBatchTx_persistent (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (W : IProp GF) : Persistent (isBatchTx bt View W) := by
  unfold isBatchTx; infer_instance

/-- `b` is a `Backend` whose `ConcurrentReadTx()` and `ReadTx()` return a snapshot reader of
the bucket the caller holds as `View q m` (any fraction `q`), which the caller keeps, and
whose `BatchTx()` is a batch transaction over the view, its lock holding `W`; `ForceCommit()`
returns (the commit to disk has no effect on the view). -/
def isKeyBackend (b : GoInterface) (View : Qp → Bucket → IProp GF) (W : IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗ keyReadSnap rt m }}) ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗ keyReadSnap rt m }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (bt : GoInterfaceOk), RET #(GoInterface.ok bt); isBatchTx bt View W }}) ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
      {{ RET #(); True }}))

instance isKeyBackend_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (W : IProp GF) : Persistent (isKeyBackend b View W) := by
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

/-- The store's view of the bucket: the ghost map's authority at fraction `q`. -/
def bucketView (γ : StoreNames) (q : Qp) (m : Bucket) : IProp GF :=
  ghostMapAuth γ.bucket q m

/-- The view as two halves (`s.revMu`'s and the batch lock's). -/
theorem bucketView_halves (γ : StoreNames) (q : Qp) (m : Bucket) :
    bucketView (GF := GF) γ q m ⊣⊢ bucketView γ q.half m ∗ bucketView γ q.half m := by
  unfold bucketView
  have h := (ghostMapAuth_fractional (GF := GF) γ.bucket m).fractional q.half q.half
  rw [Qp.half_add_half] at h
  exact h

/-- A revision token: the right to open one write transaction (`store.Write`). The store's
`NewStore` hands out `2 ^ 63 - 5` of them: with the budget `writerRes` keeps, the revision
counter stays below `2 ^ 63 - 2`. -/
def revToken (γ : StoreNames) : IProp GF := ownToks γ.revs 1

/-- A full fraction as two halves (for `currentRev`, half under `s.revMu`, half the writer's). -/
theorem own_half_half (q : Qp) : (DFrac.own q : DFrac) = DFrac.own q.half • DFrac.own q.half := by
  have h := Qp.half_add_half q
  calc (DFrac.own q : DFrac) = DFrac.own (q.half + q.half) := by rw [h]
    _ = DFrac.own q.half • DFrac.own q.half := rfl

/-! ## The locks -/


/-- The batch lock's resource for the store (`W` of `isKeyBackend`): the index writer's handle
at the committed log `ilog` with no pending change, half the committed-log ghost variable (the
other half under `s.revMu`), half of `currentRev` (`store.Write` reads it under the batch lock
alone), half the bucket's view (the other half under `s.revMu`: the write transaction's reads
of the bucket, through the batch transaction) and the certificate of `ilog`. -/
def writerRes (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (ilog : Log) (ntok : Nat),
    "Htoks" ∷ ownTokAuth γ.revs ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Hw" ∷ idxWriter γ.idx ilog [] ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketView γ (1 : Qp).half (bucketMap ilog) ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝)

/-- `s.revMu`'s resource at fraction `q`: the committed log `log`'s last revision in
`currentRev` (half of it: the writer holds the other half under the batch lock), half the
committed-log ghost variable, the index's certificate of `log` and the bucket's authority
(`bucketMap log`, half of it: the batch lock holds the other half). (`compactMainRev` is fixed at `-1`, no compaction in scope: `isStore`;
`rangeKeys` reads it without the lock.) -/
def revMuInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ log : Log,
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q.half} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hclog" ∷ ghostVar γ.clog q.half log ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "Hbucket" ∷ bucketView γ q.half (bucketMap log))

/-- Halving distributes over a sum of fractions. -/
theorem qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

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
      (ghostMapAuth_fractional (GF := GF) γ.bucket m).fractional q1.half q2.half
    unfold revMuInv bucketView
    rw [qp_half_add]
    refine ⟨?_, ?_⟩
    · iintro H
      icases H with ⟨%log, H⟩
      iNamed H
      icases (hcur _).1 $$ Hrev with ⟨Hr1, Hr2⟩
      icases (hclog log).1 $$ Hclog with ⟨Hc1, Hc2⟩
      icases (hbv _).1 $$ Hbucket with ⟨Hb1, Hb2⟩
      isplitl [Hr1 Hc1 Hb1]
      · iexists log; simp only [named]; iframe Hr1 Hc1 Hb1; iframe #; ipureintro; exact Hne
      · iexists log; simp only [named]; iframe Hr2 Hc2 Hb2; iframe #; ipureintro; exact Hne
    · iintro ⟨H1, H2⟩
      icases H1 with ⟨%log, H1⟩
      icases H2 with ⟨%log2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      ihave %Hlog := ghostVar_agree γ.clog _ _ _ _ $$ Hclog1 Hclog2
      subst Hlog
      iexists log
      simp only [named]
      isplitl [Hrev1 Hrev2]
      · iapply (hcur _).2; iframe Hrev1 Hrev2
      isplitl [Hclog1 Hclog2]
      · iapply (hclog log).2; iframe Hclog1 Hclog2
      isplitr
      · iexact Hcert1
      isplitr
      · ipureintro; exact Hne1
      iapply (hbv _).2; iframe Hbucket1 Hbucket2

/-- A store (persistent): its backend, index, lessor, logger, and the two locks' guards. The
fields `restore` and `Close` change are fixed here (out of scope). -/
def isStore (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (b le : GoInterface) (ti lg : Loc),
    "#Hb" ∷ s.[store, go!"b"] ↦□ b ∗
    "#Hbk" ∷ isKeyBackend b (bucketView γ) (writerRes s γ) ∗
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

/-- A transaction's tokens: a reader slot of each of `s.mu`, `s.revMu` and the index's lock. -/
def storeReader (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ ti : Loc,
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "Hmu" ∷ sync.ownRWMutex (muAddr s) muInv ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx)

/-! ## The read transaction -/

/-- The `storeTxnRead` of a read transaction at revision `rev` of the committed log `log`
(its fields, read-only): its reader `rt` (as `UnsafeReader` and as `ReadTx`) is a snapshot of
a bucket holding `log`'s, `firstRev` is `-1`, `rev` is `log`'s last revision. -/
def storeTxnReadIs (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames) (log : Log)
    (rev : w64) : IProp GF :=
  iprop(∃ m : Bucket,
    "#Hs" ∷ (txCommon tr).[storeTxnCommon, go!"s"] ↦□ s ∗
    "#Htxc" ∷ (txCommon tr).[storeTxnCommon, go!"tx"] ↦□ (GoInterface.ok rt : GoInterface) ∗
    "#HfirstRev" ∷ (txCommon tr).[storeTxnCommon, go!"firstRev"] ↦□ (W64 (-1) : w64) ∗
    "#Hrev" ∷ (txCommon tr).[storeTxnCommon, go!"rev"] ↦□ rev ∗
    "#Htrace" ∷ (txCommon tr).[storeTxnCommon, go!"trace"] ↦□ trace ∗
    "#Htx" ∷ tr.[storeTxnRead, go!"tx"] ↦□ (GoInterface.ok rt : GoInterface) ∗
    "#Hsnap" ∷ keyReadSnap rt m ∗
    "%Hsub" ∷ ⌜GMap.Subseteq (bucketMap log) m⌝ ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "%Hne" ∷ ⌜log ≠ []⌝ ∗
    "%Hrev" ∷ ⌜rev = W64 ((log.length : Int) - 1)⌝)

instance storeTxnReadIs_persistent (tr s : Loc) (rt : GoInterfaceOk) (trace : Loc) (γ : StoreNames)
    (log : Log) (rev : w64) : Persistent (storeTxnReadIs (GF := GF) tr s rt trace γ log rev) := by
  unfold storeTxnReadIs; infer_instance

/-- The read transaction `store.Read` returns, as the caller sees it: the `metricsTxnWrite`
wrapper at `mw` (its counters), around the `txnReadWrite` wrapper around the `storeTxnRead`,
with the transaction's tokens (`s.mu` held shared until `End`). -/
def isTxnRead (mw s : Loc) (γ : StoreNames) (log : Log) (rev : w64) : IProp GF :=
  iprop(∃ (trw tr trace ti : Loc) (rt : GoInterfaceOk) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw,
        ranges' := ranges, puts' := W64 0, deletes' := W64 0, putSize' := W64 0 } : metricsTxnWrite) ∗
    "Htrw" ∷ trw.[txnReadWrite, go!"TxnRead"] ↦
      (interface.mkOk (go.GoType.PointerType storeTxnRead.ty) #tr : GoInterface) ∗
    "#Hs" ∷ isStore s γ ∗
    "#Htr" ∷ storeTxnReadIs tr s rt trace γ log rev ∗
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

/-- What `rangeKeys(ctx, key, end, rev, ro)` returns (`r`, `err`) of the committed log `log`
at the transaction's revision `rev`, for `[k, e)` (`endNil`: no end key):
* a future revision (`ro.Rev > rev`): `ErrFutureRev` and a count of `-1`;
* the context done (a full read only): no result and an error;
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
      ⌜r = null⌝ ∗ ⌜err ≠ GoInterface.nil⌝) ∨
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
    (ps : List Loc) (ntok : Nat),
    "Htoks" ∷ ownTokAuth γ.revs ntok ∗
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
    "#Hbt" ∷ batchTxSpec bt (bucketView γ) (writerRes s γ) Locked ∗
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
    "Hti" ∷ idxReader ti γ.idx)

/-- The write transaction `store.Write` returns, as the caller sees it: the `metricsTxnWrite`
wrapper at `mw` (its counters `puts`, `deletes`, `putSize`) around the `storeTxnWrite`. -/
def isTxnWrite (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) : IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteIs tw s γ ilog pend)

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

/-- What `End` leaves of a transaction: nothing of a read one; of a write one, the
certificate of the committed log. -/
def txnEndPost (γ : StoreNames) : TxnKind → IProp GF
  | .read _ _ => iprop(True)
  | .write ilog pend _ _ _ => idxCert γ.idx (commitLog ilog pend)

/-- The store's `writeView` (`kv_view.go`): its `kv` is the store `s`. -/
def isWriteView (wv s : Loc) (γ : StoreNames) : IProp GF :=
  iprop("#Hkv" ∷ wv.[writeView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType store.ty) #s : GoInterface) ∗
    "#Hs" ∷ isStore s γ)

instance isWriteView_persistent (wv s : Loc) (γ : StoreNames) :
    Persistent (isWriteView (GF := GF) wv s γ) := by
  unfold isWriteView; infer_instance


end reprs

end mvcc
end EtcdGrove
end Perennial
