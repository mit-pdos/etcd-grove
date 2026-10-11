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

/-- `s.mu`'s resource: nothing (see the module docstring); it takes the semantics' instances
(unused) so that the lock lemmas' own are determined at its uses. -/
def muInv [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
    [AllG GF] [sem : go.Semantics] (_q : Qp) : IProp GF := iprop(True)

instance muInv_fractional [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] [AllG GF] [sem : go.Semantics] : Fractional (muInv (hG := hG)) where
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

end addrs

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
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

/-- `b` is a `Backend` whose `ConcurrentReadTx()` and `ReadTx()` return a snapshot reader of
the bucket the caller holds as `View q m` (any fraction `q`), which the caller keeps. -/
def isKeyBackend (b : GoInterface) (View : Qp → Bucket → IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m }} (App (Val #(methods bi.ty go!"ConcurrentReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗ keyReadSnap rt m }}) ∗
    □ (∀ (q : Qp) (m : Bucket),
      {{ View q m }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
      {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); View q m ∗ keyReadSnap rt m }}))

instance isKeyBackend_persistent (b : GoInterface) (View : Qp → Bucket → IProp GF) :
    Persistent (isKeyBackend b View) := by
  unfold isKeyBackend; infer_instance

/-- The store's view of the bucket: the ghost map's authority at fraction `q`. -/
def bucketView (γ : StoreNames) (q : Qp) (m : Bucket) : IProp GF :=
  ghostMapAuth γ.bucket q m

/-! ## The locks -/


/-- `s.revMu`'s resource at fraction `q`: the committed log `log`'s last revision in
`currentRev`, no compaction, the index's certificate of `log` and the bucket's authority
(`bucketMap log`). -/
def revMuInv (s : Loc) (γ : StoreNames) (q : Qp) : IProp GF :=
  iprop(∃ log : Log,
    "Hrev" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own q} (W64 ((log.length : Int) - 1) : w64) :
      IProp GF) ∗
    "Hcmp" ∷ (s.[store, go!"compactMainRev"] ↦{DFrac.own q} (W64 (-1) : w64) : IProp GF) ∗
    "#Hcert" ∷ idxCert γ.idx log ∗
    "Hbucket" ∷ bucketView γ q (bucketMap log))

/-- A store (persistent): its backend, index, logger, and the two locks' guards. The fields
`restore` and `Close` change are fixed here (out of scope). -/
def isStore (s : Loc) (γ : StoreNames) : IProp GF :=
  iprop(∃ (b : GoInterface) (ti lg : Loc),
    "#Hb" ∷ s.[store, go!"b"] ↦□ b ∗
    "#Hbk" ∷ isKeyBackend b (bucketView γ) ∗
    "#Hidx" ∷ s.[store, go!"kvindex"] ↦□
      (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
    "#Hti" ∷ isTreeIndex ti γ.idx ∗
    "#Hlg" ∷ s.[store, go!"lg"] ↦□ lg ∗
    "#Hmu" ∷ sync.isRWMutexGuard (muAddr s) muInv ∗
    "#HrevMu" ∷ sync.isRWMutexGuard (revMuAddr s) (revMuInv s γ))

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

end reprs

end mvcc
end EtcdGrove
end Perennial
