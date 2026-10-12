/-
The database and its read transactions (sequential use: one goroutine at a time uses the
database, with any number of read transactions open and at most one writer).

**The state.** `DBState`: the file (`fd`, its bytes `bs`) and its mapping (`data`, `sz`), the
page size, the freelist's state, and the open readers (a map from a ghost key to each
reader's `Reader`: its txid, its tree's root and high-water mark, the pages it sees and its
fraction `q` of them).

**The mapping's cells.** The caller's half of each mapped slot (`FilePages.lean`) is shared:
the database holds `rem s` of slot `s` and every reader that sees `s` holds its `q` (the
pages it sees, `pagesView`): `slotsOK`. The fields `data` and `pageSize` are shared the same
way (`fieldsOK`). A reader's pages are the file's (`pagesOf`): the database never changes a
slot a reader sees, which is bbolt's MVCC rule (`mvccOK`: such a slot is no meta page, not
free, and pending only from a transaction newer than the reader).

**The logger** is the default one (`discardLogger`, nil standing for it): a logger contract
is later work, so `Begin` and the others never log.

**The locks.** `mmaplock` (an RWMutex) protects the mapping against a remap: its invariant is
a ghost token (`mmapTok`); each open reader holds a read lock, and its `mmapTok γ rfrac` is
kept here (`Htoks`), so a writer holding the write lock (`mmapTok γ 1`) knows that no reader
is open. `metalock` (a Mutex) protects nothing more in sequential use. `statlock` (an RWMutex)
protects the statistics, which in sequential use are simply the database's (`statsInv` is
`True`). The database holds the unused read handles of
`mmaplock` (`ownRWMutex`, one per reader that can still begin, `rwmutex.actualMaxReaders` in
all) and one of `statlock`.
-/
module

public import Proof.go_etcd_io.bbolt.DBSplit
public import Proof.go_etcd_io.bbolt.DBModel
public import Proof.go_etcd_io.bbolt.FilePages
public import Proof.go_etcd_io.bbolt.Tx__init
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Proof.os.FileModel
public import Proof.go_etcd_io.bbolt.internal.freelist.Iface
public import Perennial.Proof.sync_proof.mutex
public import Perennial.Proof.sync_proof.rwmutex_guard
public import Perennial.Ghost.GhostMap
public import Proof.sync.PoolModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt sync

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- An open read transaction, as the database accounts for it. -/
structure Reader where
  txid : w64
  root : Nat
  hwm : Nat
  pages : GMap Nat (List w8)
  q : Qp

noncomputable instance countableRat : Pos.Countable Rat :=
  .ofInjective (fun r => Pos.Countable.encode (r.num, r.den)) (fun a b h => by
    have h' := Pos.encode_inj h
    exact Rat.ext (congrArg Prod.fst h') (congrArg Prod.snd h'))

noncomputable instance countableQp : Pos.Countable Qp :=
  .ofInjective (fun q => Pos.Countable.encode q.val) (fun a b h => Qp.ext_iff.2 (Pos.encode_inj h))

noncomputable instance countableReader : Pos.Countable Reader :=
  .ofInjective (fun r => Pos.Countable.encode (r.txid, r.root, r.hwm, r.pages, r.q)) (fun a b h => by
    have h' := Pos.encode_inj h
    cases a; cases b; simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

/-- The database's state. -/
structure DBState where
  file : Loc
  fd : w64
  bs : List w8
  data : Loc
  sz : Nat
  ps : Nat
  fl : FLState
  readers : GMap Nat Reader
  /-- The database's fraction of each slot. -/
  rem : Nat → Qp
  /-- The database's fraction of the fields `data`, `pageSize`. -/
  frem : Qp
  /-- The open writer (`db.rwtx`, null if none) and its view of the current tree: accounted
  for as a reader is (it reads the pages it does not rewrite), but no read-only transaction
  of the freelist and no holder of a read lock. -/
  rwtx : Loc
  wr : Option Reader

/-- The number of whole slots the mapping holds of the file. -/
def DBState.nslots (σ : DBState) : Nat := min σ.sz σ.bs.length / σ.ps

/-- Adding fractions, `none` being none. -/
def optAdd (a : Qp) : Option Qp → Option Qp
  | none => some a
  | some b => some (a + b)

/-- The sum of the fractions `q` of the readers `rs` that `sees` (`none`: no reader). -/
def readersQ (rs : GMap Nat Reader) (sees : Reader → Bool) : Option Qp :=
  GMap.mapFold (fun _ r acc => if sees r then optAdd r.q acc else acc) none rs

open Classical in
/-- Reader `r` sees slot `s`. -/
def Reader.sees (r : Reader) (s : Nat) : Bool := decide (coversSlot r.pages s)

/-- `a` and the fractions `o` make up `whole`. -/
def fracSum (a : Qp) (o : Option Qp) (whole : Qp) : Prop :=
  match o with
  | none => a = whole
  | some s => a + s = whole

/-- The writer's fraction added to `o` where it `sees`. -/
def wQ (wr : Option Reader) (sees : Reader → Bool) (o : Option Qp) : Option Qp :=
  match wr with
  | none => o
  | some w => if sees w then optAdd w.q o else o

/-- The slots: the database's part and the readers' (and the writer's) make up the caller's
half. -/
def slotsOK (σ : DBState) : Prop :=
  ∀ s < σ.nslots,
    fracSum (σ.rem s) (wQ σ.wr (fun r => r.sees s) (readersQ σ.readers (fun r => r.sees s))) halfQ

/-- The shared fields: the database's part and every reader's (and the writer's) make up the
whole. -/
def fieldsOK (σ : DBState) : Prop :=
  fracSum σ.frem (wQ σ.wr (fun _ => true) (readersQ σ.readers (fun _ => true))) 1

/-- A reader's pages are the file's, inside the mapping and below its high-water mark, and
form its well-formed tree. -/
def readerOK (σ : DBState) (r : Reader) : Prop :=
  treeWF r.pages r.hwm r.root ∧ pagesDisjoint r.pages ∧
  (∀ id pg, r.pages !! id = some pg →
    pageAt σ.bs σ.ps id = pg ∧ id + pageSpan σ.bs σ.ps id ≤ min σ.nslots r.hwm)

/-- bbolt's MVCC rule, for a view of transaction `txid` (a reader's, or the writer's) of the
pages `pages`: they were allocated by `txid` or before (`allocs`); a slot they cover is no meta
page, not free, and pending only from a transaction newer than `txid` that freed a page
allocated by `txid` or before. So a page allocated and freed between two views is seen by
neither (`releaseRange` frees it), and one freed before every view is seen by none
(`release`). -/
def mvccView (σ : DBState) (txid : w64) (pages : GMap Nat (List w8)) : Prop :=
  (∀ id pg, pages !! id = some pg → ∀ a, σ.fl.allocs !! W64 id = some a → uint.Z a ≤ uint.Z txid) ∧
  ∀ s, coversSlot pages s → 2 ≤ s ∧ W64 s ∉ σ.fl.free ∧
    ∀ t pd a, σ.fl.pending !! t = some pd → (W64 s, a) ∈ pd.pairs →
      uint.Z a ≤ uint.Z txid ∧ uint.Z txid < uint.Z t

/-- Every reader's view keeps the MVCC rule. -/
def mvccOK (σ : DBState) : Prop :=
  ∀ k r, σ.readers !! k = some r → mvccView σ r.txid r.pages

/-- The writer: its view is a reader's (`readerOK`, MVCC: the pages it frees go pending for
its own transaction, newer than its view), and it exists exactly when `rwtx` is set. -/
def writerOK (σ : DBState) : Prop :=
  (σ.wr = none ↔ σ.rwtx = null) ∧
  ∀ w, σ.wr = some w → readerOK σ w ∧ mvccView σ w.txid w.pages

/-- The meta in slot `s`'s bytes after the page header. -/
def metaIn (σ : DBState) (s : Nat) (v : internal.common.Meta) : Prop :=
  ((slotAt σ.bs σ.ps s).drop 16).take 64 = metaBytes v

/-- The freelist's ids are below the high-water mark of the current meta `m`: the free ones,
and the pending ones of committed transactions (`m`'s and before; the open writer's own, newer,
may have been allocated above it). Without a writer every pending transaction is committed;
the writer's view is of `m`. (bbolt never writes a freelist breaking this, but reads one from
the file: `node.spill` panics on a page id at the high-water mark or above.) -/
def flBelow (σ : DBState) (m : internal.common.Meta) : Prop :=
  (∀ x ∈ σ.fl.free, uint.Z x < uint.Z m.pgid') ∧
  (∀ t pd p, σ.fl.pending !! t = some pd → p ∈ pd.pairs → uint.Z t ≤ uint.Z m.txid' →
    uint.Z p.1 < uint.Z m.pgid') ∧
  (σ.wr = none → ∀ t pd p, σ.fl.pending !! t = some pd → p ∈ pd.pairs →
    uint.Z t ≤ uint.Z m.txid') ∧
  (∀ w, σ.wr = some w → w.hwm = uint.nat m.pgid')

/-- The current tree (of the meta `db.meta()` picks): well-formed, its pages disjoint, inside
the mapping and below the high-water mark, allocated by its transaction or before, and none
free or pending (a new reader sees it, `mvccOK`); the freelist below its high-water mark. -/
def currentOK (σ : DBState) (v0 v1 : internal.common.Meta) : Prop :=
  let m := if metaPick v0 v1 then v1 else v0
  let hwm := uint.nat m.pgid'
  let root := uint.nat m.root'.root'
  let ps := treePages (filePages σ.bs σ.ps hwm) root
  treeWF ps hwm root ∧ pagesDisjoint ps ∧
  (∀ id pg, ps !! id = some pg → id + pageSpan σ.bs σ.ps id ≤ min σ.nslots hwm) ∧
  (∀ id pg, ps !! id = some pg → ∀ a, σ.fl.allocs !! W64 id = some a →
    uint.Z a ≤ uint.Z m.txid') ∧
  (∀ s, coversSlot ps s → 2 ≤ s ∧ W64 s ∉ σ.fl.free ∧
    ∀ t pd a, σ.fl.pending !! t = some pd → (W64 s, a) ∉ pd.pairs) ∧
  flBelow σ m

/-- The database's facts: the mapping, the two metas (one valid), the current tree, the
readers, the accounting. -/
def dbOK (σ : DBState) (v0 v1 : internal.common.Meta) : Prop :=
  80 ≤ σ.ps ∧ σ.ps < 2 ^ 32 ∧ 2 ≤ σ.nslots ∧ σ.sz < 281474976710655 ∧ σ.data.locCar ≠ 0 ∧
  metaIn σ 0 v0 ∧ metaIn σ 1 v1 ∧ (metaValid v0 ∨ metaValid v1) ∧ currentOK σ v0 v1 ∧
  (∀ k r, σ.readers !! k = some r → readerOK σ r) ∧ mvccOK σ ∧ slotsOK σ ∧ fieldsOK σ ∧
  σ.fl.readonly.Perm (σ.readers.toList.map (·.2.txid)) ∧
  σ.readers.size < Int.toNat rwmutex.actualMaxReaders ∧ writerOK σ

/-- The database's part of its `freelist` field: all of it, or half if a writer is open (which
holds the other half: it frees and allocates pages through it). -/
def flfQ (rwtx : Loc) : Qp := if rwtx = null then 1 else halfQ

theorem flfQ_null : flfQ null = halfQ + halfQ := by
  simp [flfQ, halfQ, Qp.half_add_half]

/-- The caller's half of the mapped cells after the whole slots (inside the file): no reader
sees them, and a remap gives them back with the slots (`munmap` takes the whole mapping). -/
def mapTail (data : Loc) (bs : List w8) (sz ps : Nat) : IProp GF :=
  bytesPointsto (data +ₗ (((min sz bs.length / ps) * ps : Nat) : Int)) (DFrac.own halfQ)
    ((bs.take sz).drop ((min sz bs.length / ps) * ps))

/-- What the page pool holds: zeroed byte slices of a page (`Tx.write` zeroes a page before
putting it back; `New` makes one). -/
def pageBuf (ps : Nat) (v : GoInterface) : IProp GF :=
  iprop(∃ (s : GoSlice), ⌜v = interface.mkOk (go.GoType.SliceType go.byte) #s⌝ ∗
    s ↦* List.replicate ps (W8 0))

/-- `mmaplock`'s invariant: a ghost token. -/
def mmapTok (γ : GName) (q : Qp) : IProp GF := ghostVar γ q ()

/-- `statlock`'s invariant: nothing (in sequential use the statistics are the database's). -/
def statsInv (_q : Qp) : IProp GF := iprop(True)

/-- The ghost names of a database. -/
structure DBNames where
  mmap : GName
  readers : GName

/-- The database at `dbl` (sequential use), its freelist an implementation `I`
of the freelist interface. -/
def ownDB (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) : IProp GF :=
  iprop(∃ (dv : DB) (fls : Loc) (v0 v1 : internal.common.Meta) (dl : Loc),
    "%Hdv" ∷ ⌜dv.data' = σ.data ∧ dv.pageSize' = W64 σ.ps ∧ dv.datasz' = W64 σ.sz ∧
      dv.meta0' = σ.data +ₗ 16 ∧ dv.meta1' = σ.data +ₗ ((σ.ps + 16 : Nat) : Int) ∧
      dv.opened' = true ∧ dv.file' = σ.file ∧ dv.freelist' = I.iface ∧ dv.rwtx' = σ.rwtx ∧
      dbl ≠ null⌝ ∗
    "%Hok" ∷ ⌜dbOK σ v0 v1⌝ ∗
    "%Hdr" ∷ ⌜dv.dataref' = slice.mk σ.data (W64 σ.sz) (W64 σ.sz)⌝ ∗
    "#Hdl" ∷ (globalAddr discardLogger ↦□ dl : IProp GF) ∗
    "#Hdlok" ∷ defaultLoggerOK dl ∗
    "%Hlog" ∷ ⌜dv.logger' = interface.nil ∨
      dv.logger' = interface.mkOk (go.GoType.PointerType DefaultLogger.ty) #dl⌝ ∗
    "Hplain" ∷ dbPlain dbl (DFrac.own 1) dv ∗
    "#Hlogger" ∷ structFieldRef DB go!"logger" dbl ↦□ dv.logger' ∗
    "#HMlock" ∷ structFieldRef DB go!"Mlock" dbl ↦□ false ∗
    "Hflf" ∷ structFieldRef DB go!"freelist" dbl ↦{DFrac.own (flfQ σ.rwtx)} dv.freelist' ∗
    "Hdata" ∷ structFieldRef DB go!"data" dbl ↦{DFrac.own σ.frem} σ.data ∗
    "#Hps" ∷ structFieldRef DB go!"pageSize" dbl ↦□ W64 σ.ps ∗
    "#Hpool" ∷ isPool (structFieldRef DB go!"pagePool" dbl) (pageBuf σ.ps) ∗
    "#Hfile" ∷ osFile σ.file σ.fd ∗
    "Hbytes" ∷ fileBytes σ.fd σ.bs ∗
    "Hmap" ∷ fileMap σ.fd (some (σ.data, σ.sz)) ∗
    "Hslots" ∷ slotsView σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ∗
    "Htail" ∷ mapTail σ.data σ.bs σ.sz σ.ps ∗
    "Hfl" ∷ ownFL I fls σ.fl ∗
    "#Hmetalock" ∷ isMutex (structFieldRef DB go!"metalock" dbl) iprop(True) ∗
    "#Hrwlock" ∷ isMutex (structFieldRef DB go!"rwlock" dbl) iprop(True) ∗
    "Hrwl" ∷ (if decide (σ.rwtx = null) then emp else ownMutex (structFieldRef DB go!"rwlock" dbl)) ∗
    "Hmmaph" ∷ ([∗list] _x ∈ List.replicate (Int.toNat rwmutex.actualMaxReaders - σ.readers.size) (),
      ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap)) ∗
    "Htoks" ∷ ([∗map] _k ↦ _r ∈ σ.readers, mmapTok γ.mmap rfrac) ∗
    "Hstath" ∷ ownRWMutex (structFieldRef DB go!"statlock" dbl) statsInv ∗
    "Hstats" ∷ (⌜dv.stats' = null⌝ ∨ ∃ (sv : Stats), dv.stats' ↦ sv) ∗
    "Hrauth" ∷ ghostMapAuth γ.readers 1 σ.readers)

/-- The read transaction at `txl` of the database at `dbl`, which accounts for it as `r` under
the key `k` (`managed`: inside `View`, where `Rollback` panics). -/
def ownReadTx (dbl : Loc) (γ : DBNames) (txl : Loc) (k : Nat) (r : Reader) (data : Loc)
    (ps : Nat) (managed : Bool) : IProp GF :=
  iprop(∃ (t : Tx) (mv : internal.common.Meta),
    "Htx" ∷ txl ↦ t ∗
    "%Ht" ∷ ⌜t.db' = dbl ∧ t.writable' = false ∧ t.pages' = map.nil ∧ t.managed' = managed ∧
      t.root'.tx' = txl ∧ t.root'.buckets' = map.nil ∧ t.root'.nodes' = map.nil ∧
      t.root'.page' = null ∧ t.root'.rootNode' = null ∧
      mv.txid' = r.txid ∧ uint.nat mv.root'.root' = r.root ∧ uint.nat mv.pgid' = r.hwm⌝ ∗
    "Hmeta" ∷ t.meta' ↦ mv ∗
    "Hroot" ∷ t.root'.InBucket' ↦ mv.root' ∗
    "Hrdata" ∷ structFieldRef DB go!"data" dbl ↦{DFrac.own r.q} data ∗
    "#Hrps" ∷ structFieldRef DB go!"pageSize" dbl ↦□ W64 ps ∗
    "Hpages" ∷ pagesView data ps r.q r.pages ∗
    "Hrl" ∷ ownRWMutexRLocked (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap) ∗
    "Hkey" ∷ k ↪[γ.readers] r)

end defs

end bbolt
end EtcdGrove
end Perennial
