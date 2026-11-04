/-
The resources of bbolt's locks (U0a of `notes/bbolt-proof-plan.md`; design §3.4, §3.5):
`metalock`'s (`metaR`), `mmaplock`'s guarded fractional resource (`Pm`), `statlock`'s (`Ps`), and
`rwlock`'s (`rwR`): the writer's database side while idle (`wdbOwn`, its pure state `WDb` with
`wdbOK`), or closed (`closedR`). `wdbOpen` is `Open`'s writer side before `loadFreelist`.

(U0a deviations: `rwR` and `wdbOwn` take the stats pointer `sp` and the receipt base `t0`, for
the spare pair and the receipts, which the design leaves implicit; the file is owned through its
fields (`fileOwn`, equal to `os.ownFile`), since `os.ownFile` takes `os.Assumptions`, which the
sealed predicates cannot.)
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.Model.Store
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.GooseLang.Receipts
public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section locks
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## Fields and cells -/

omit go_gctx hos sem in
/-- A pure fact, at any fraction (`mapFields`' length bound). -/
instance pure_dfractional (P : Prop) :
    DFractional (fun (_ : DFrac) => (iprop(⌜P⌝) : IProp GF)) where
  dfractional _ _ := ⟨persistent_sep_dup.1.trans (sep_mono .rfl .rfl), sep_elim_left⟩
  dfractional_persistent := inferInstance
  dfractional_persist _ := bupd_intro

/-- The mapping fields of `db` in the state `ms` (`invalidate` clears them). A mapping is at most
`maxMapSize` (`0xFFFFFFFFFFFF`) long: `DB.mmap` maps `db.mmapSize(…)`'s result, which caps it there
(or fails); `db.page`'s index into `*[maxMapSize]byte` needs it (U6 fix, for `Tx.page_r`). Its base
is a mapped address, `0 < base.addr` (`DB.mmap` gets it from `unix.Mmap`'s cells; `DB.page`'s
`arrayIndexRef` needs it, batch 9). Its length is whole pages, or `maxMapSize` (batch 15:
`mmapSize` doubles up to 1 GiB, then rounds up to a GiB, then caps at `maxMapSize`), so that the
cells of `[0, len)` are the slots' and the partial last slot's (`wCells`). -/
def mapFields (db : Loc) (dq : DFrac) : MapSt → IProp GF
  | some (base, len) => iprop(
      db.[DB, go!"dataref"] ↦{dq} (⟨base, W64 (len : Int), W64 (len : Int)⟩ : GoSlice) ∗
      db.[DB, go!"data"] ↦{dq} base ∗
      db.[DB, go!"meta0"] ↦{dq} (base +ₗ (16 : Int)) ∗
      db.[DB, go!"meta1"] ↦{dq} (base +ₗ (4112 : Int)) ∗
      ⌜len ≤ 0xFFFFFFFFFFFF ∧ 0 < base.addr ∧ (len % 4096 = 0 ∨ len = 0xFFFFFFFFFFFF)⌝)
  | none => iprop(db.[DB, go!"dataref"] ↦{dq} slice.nil ∗ db.[DB, go!"data"] ↦{dq} null ∗
      db.[DB, go!"meta0"] ↦{dq} null ∗ db.[DB, go!"meta1"] ↦{dq} null)

/-- The client halves' share `q` of the two meta slots' cells, holding `C`'s metas (nothing
while unmapped). -/
def metaCellsQ (q : Qp) (ms : MapSt) (C : CommitSt) : IProp GF :=
  match ms with
  | some (base, _) => iprop(bytesPointsto base (DFrac.own q) C.m0 ∗
      bytesPointsto (base +ₗ (4096 : Int)) (DFrac.own q) C.m1)
  | none => iprop(emp)

/-- A share of the meta slots' page-cache bytes, holding `C`'s metas (clean or not). -/
def metaOsBytes (p : GoString) (dq : DFrac) (C : CommitSt) : IProp GF :=
  iprop(∃ xs : List (w8 × Bool), osBytes p 0 dq xs ∗ ⌜xs.map Prod.fst = C.m0 ++ C.m1⌝)

/-- The `*os.File` `f` is open on `fd`, named `name` (`os.ownFile`'s body, `fileOwn_eq`). -/
def fileOwn (f : Loc) (fd : w64) (name : GoString) (dq : DFrac) : IProp GF :=
  iprop(∃ inner : Loc, f ↦□ (os.File.mk inner) ∗
    structFieldRef os.file go!"fd" inner ↦{dq} fd ∗
    structFieldRef os.file go!"name" inner ↦□ name)

theorem fileOwn_eq [os.Assumptions] (f : Loc) (fd : w64) (name : GoString) (dq : DFrac) :
    fileOwn (GF := GF) f fd name dq = os.ownFile f fd name dq := rfl

/-! ## `metalock` -/

/-- The freelist's reader part, only when there is a freelist (round 2, F1/O4, F4.6): the
physical `readonlyTXIDs` is `F`'s values as a multiset. -/
def flRoOpt (fli : GoInterface) (F : GMap Nat w64) : IProp GF :=
  if fli = interface.nil then iprop(emp)
  else iprop(∃ ro, flRoOwn fli ro ∗ ⌜ro.Perm (F.toList.map Prod.snd)⌝)

/-- **`metalock`'s resource**: half of the committed state and a quarter of the data, the
closed flag, halves of `opened`/`freelist`/`ops.writeAt`, half of the meta slots' page-cache
bytes (while open), the meta-borrow token `mlk`, the readers' txids `F` with the freelist's
reader part, and, while open, the committed state's well-formedness; the txids are at least 1
(U3 finding 6: `ReleasePendingPages` computes `t - 1` of each, which wraps at 0). -/
def metaR (B : BNs) (db : Loc) (p : GoString) : IProp GF :=
  iprop(∃ (C : CommitSt) (F : GMap Nat w64) (cl : Bool) (fli : GoInterface) (wa : GoFunc),
    ghostVar B.cur (1 : Qp).half C ∗ ghostVar B.st (1 : Qp).half.half (treeData C) ∗
    ghostVar B.cls (1 : Qp).half cl ∗
    db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} (!cl) ∗
    db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} fli ∗
    (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half} wa ∗
    (if cl then iprop(emp) else metaOsBytes p (DFrac.own (1 : Qp).half) C) ∗
    ghostVar B.mlk 1 () ∗ ghostMapAuth B.fltx 1 F ∗ flRoOpt fli F ∗
    ⌜cl = false → C.metaOk ∧ treeOK C ∧ 1 ≤ C.txid⌝ ∗ ⌜∀ k t, F !! k = some t → 1 ≤ t.toNat ∧ t.toNat ≤ C.txid⌝)

/-! ## `mmaplock` and `statlock` -/

/-- **`mmaplock`'s guarded resource** at fraction `q` (`RLock` gives `Pm rfrac`, `Lock` gives
`Pm 1`): a share of the mapping's state and fields, and `q` of the token `mtok`. -/
def Pm (B : BNs) (db : Loc) (q : Qp) : IProp GF :=
  iprop(∃ ms : MapSt, ghostVar B.map q.half.half ms ∗ mapFields db (DFrac.own q.half) ms ∗
    ghostVar B.mtok q ())

/-- `mmaplock`'s resource without the token (what a registered reader keeps: its `mtok rfrac`
is deposited in `pagesInv`). -/
def PmNoTok (B : BNs) (db : Loc) (q : Qp) : IProp GF :=
  iprop(∃ ms : MapSt, ghostVar B.map q.half.half ms ∗ mapFields db (DFrac.own q.half) ms)

/-- **`statlock`'s guarded resource**: the database's statistics (none if `db.stats` is nil). -/
def Ps (sp : Loc) (q : Qp) : IProp GF :=
  if sp = null then iprop(emp) else iprop(∃ s : Stats, sp ↦{DFrac.own q} s)

/-- A reader-token pair of `mmaplock` and `statlock` (what the pool lends, and the spare). -/
def rdPair (B : BNs) (db sp : Loc) : IProp GF :=
  iprop(sync.ownRWMutex db.[DB, go!"mmaplock"] (Pm B db) ∗
    sync.ownRWMutex db.[DB, go!"statlock"] (Ps sp))

/-! ## `rwlock` -/

/-- **The writer side's pure state**: the committed state, the freelist, the mapping, the
file's `OsMeta`, the `W` slots and their page-cache bytes `wb`, the freelist interface, a leaked
mapping (B6.1), the file and its fd. -/
structure WDb where
  C : CommitSt
  fl : FLPg
  ms : MapSt
  m : OsMeta
  W : List Nat
  wb : Nat → List w8
  fli : GoInterface
  junk : Option (Loc × Nat)
  f : Loc
  fd : w64

/-- The bytes of the extent starting at slot `f`, read from the slots' bytes `wb`. -/
def extentBytes (wb : Nat → List w8) (f : Nat) : List w8 :=
  (List.range' f (1 + pageOverflow (wb f))).flatMap wb

/-- The writer's cells of the `W` slots inside the mapping (batch 24: after `DB.grow` the file
may extend past the mapping; a slot past it has only its page-cache bytes, `wBytes`, until a
remap maps the file), and of the mapping's partial last slot (batch 15: a mapping of
`maxMapSize` ends 4095 bytes into a slot, which is no store slot and whose `W` slot, if any, has
no whole cells), the client halves, any values. -/
def wCells (ms : MapSt) (W : List Nat) : IProp GF :=
  match ms with
  | some (base, len) => iprop(([∗list] s ∈ W, if 4096 * (s + 1) ≤ len then
        iprop(∃ vf, cellsR base (4096 * s) 4096 vf) else iprop(emp)) ∗
      ∃ vf, cellsR base (4096 * (len / 4096)) (len % 4096) vf)
  | none => iprop(emp)

/-- The writer's page-cache bytes of the `W` slots inside the file (`osBytes` whole), the partial
last slot's too (batch 9: a file truncated to `growSize + AllocSize` need not end on a page). -/
def wBytes (p : GoString) (W : List Nat) (wb : Nat → List w8) (size : Nat) : IProp GF :=
  iprop([∗list] s ∈ W, if 4096 * (s + 1) ≤ size then
    iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗
      ⌜xs.map Prod.fst = wb s⌝)
    else if 4096 * s < size then
      iprop(∃ xs : List (w8 × Bool), osBytes p (4096 * s) (DFrac.own 1) xs ∗
        ⌜xs.map Prod.fst = (wb s).take (size - 4096 * s)⌝)
    else iprop(emp))

/-- **The writer side's facts** (design §3.5). -/
def wdbOK (w : WDb) : Prop :=
  (∀ b l, w.ms = some (b, l) → w.m.maps = GMap.singleton b l) ∧
  (w.ms = none → w.m.maps = ∅ ∨ ∃ jb jl, w.junk = some (jb, jl) ∧
    w.m.maps = GMap.singleton jb jl) ∧
  w.C.hwm * 4096 ≤ w.m.size ∧
  -- the `W` slots: the complement of the store slots and the metas, below the mapping or file
  (∀ s, s ∈ w.W ↔ 2 ≤ s ∧ s < max (mapLen w.ms) w.m.size / 4096 ∧ s ∉ treeSlots w.C ∧
    s ∉ pendSlots w.fl) ∧
  -- B2: within `[2, hwm)`, free ids are neither tree nor pending slots (the rest are leaked)
  (∀ x ∈ w.fl.free, x.toNat ∉ treeSlots w.C) ∧
  -- F4.2: the synced freelist page can be reloaded
  (∀ f, w.C.flpg = some f → flCurOK w.fl w.C (extentBytes w.wb f)) ∧
  -- the writer's txid and the high-water mark do not wrap (batch 6, `Free`'s pending entry of
  -- `C.txid + 1`: `treeOK`'s `txid < 2 ^ 63`, the current meta's `pgid`)
  w.C.txid + 1 < 2 ^ 64 ∧ w.C.hwm < 2 ^ 64

/-- The writer side but its share of the data, its freelist object, spare pair and receipts:
`db.rwtx` is `rw` and the writer's part of the store's state `ws` (idle, or a live writer's,
`wdbLive`), and its share `mq` of the mapping fields (½ idle; ¼ live, the writer's fractions
holding the other quarter, `wtxFrac`). -/
def wdbCoreG (B : BNs) (db : Loc) (p : GoString) (rw : Loc) (ws : WSt) (mq : Qp) (w : WDb) :
    IProp GF :=
  iprop(∃ wa : GoFunc,
    ghostVar B.cur (1 : Qp).half.half w.C ∗
    ghostVar B.fl (1 : Qp).half w.fl ∗ ghostVar B.map (1 : Qp).half w.ms ∗
    ghostVar B.out (1 : Qp).half false ∗ ghostVar B.wv (1 : Qp).half ws ∗
    db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} w.fli ∗
    db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true ∗
    (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half} wa ∗
    db.[DB, go!"rwtx"] ↦ rw ∗ db.[DB, go!"file"] ↦ w.f ∗ db.[DB, go!"path"] ↦ p ∗
    db.[DB, go!"datasz"] ↦ W64 (mapLen w.ms : Int) ∗
    mapFields db (DFrac.own mq) w.ms ∗
    osMeta p (DFrac.own 1) (some w.m) ∗ fileOwn w.f w.fd p (DFrac.own 1) ∗
    osFd w.fd (DFrac.own 1) ⟨p, true, true⟩ ∗
    metaCellsQ (1 : Qp).half.half w.ms w.C ∗ metaOsBytes p (DFrac.own (1 : Qp).half) w.C ∗
    wCells w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗
    (match w.junk with
     | some (jb, jl) => iprop(∃ vf, cellsR jb 0 jl vf)
     | none => iprop(emp)))

/-- The idle writer side's core: no `rwtx`, no live writer. -/
def wdbCore (B : BNs) (db : Loc) (p : GoString) (w : WDb) : IProp GF :=
  wdbCoreG B db p null wIdle (1 : Qp).half w

/-- **The writer side's resources** (design §3.5): `wdbCore`, its quarter of the data, the
freelist object but its reader part, the spare reader-token pair, and the receipts
`⧗ (C.txid - t0)`. -/
def wdbOwn (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (w : WDb) : IProp GF :=
  iprop(wdbCore B db p w ∗ ghostVar B.st (1 : Qp).half.half (treeData w.C) ∗
    flPgOwn w.fli w.fl ∗ rdPair B db sp ∗ receipt (w.C.txid - t0))

/-- **A live writer's database side** (in its exclusive part, `txExcl`): `db.rwtx` is the
transaction `tx`, the store's writer state `ws`; its quarter of the data is in `wtxFrac`. -/
def wdbLive (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (ws : WSt)
    (w : WDb) : IProp GF :=
  iprop(wdbCoreG B db p tx ws (1 : Qp).half.half w ∗ flPgOwn w.fli w.fl ∗ rdPair B db sp ∗
    receipt (w.C.txid - t0))

/-- **`Open`'s writer side before `loadFreelist`** (design §3.11, core phase): `wdbCore` and the
data's quarter, with no freelist (`fl = ∅`, `db.freelist` nil). -/
def wdbOpen (B : BNs) (db : Loc) (p : GoString) (w : WDb) : IProp GF :=
  iprop(wdbCore B db p w ∗ ghostVar B.st (1 : Qp).half.half (treeData w.C) ∗
    ⌜w.fl = FLPg.empty ∧ w.fli = interface.nil⌝)

/-- **A closed database's writer side**: the other halves of the ghost state and of the fields
`Close` wrote. -/
def closedR (B : BNs) (db : Loc) : IProp GF :=
  iprop(ghostVar B.cls (1 : Qp).half true ∗ ∃ (C : CommitSt) (fl : FLPg) (ms : MapSt),
    ghostVar B.cur (1 : Qp).half.half C ∗ ghostVar B.st (1 : Qp).half.half (treeData C) ∗
    ghostVar B.fl (1 : Qp).half fl ∗ ghostVar B.map (1 : Qp).half ms ∗
    mapFields db (DFrac.own (1 : Qp).half) ms ∗
    ghostVar B.out (1 : Qp).half false ∗ ghostVar B.wv (1 : Qp).half wIdle ∗
    db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} false ∗
    db.[DB, go!"freelist"] ↦{DFrac.own (1 : Qp).half} interface.nil ∗
    (∃ wa : GoFunc, (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{DFrac.own (1 : Qp).half} wa))

/-- **`rwlock`'s resource**: the writer's database side while idle, or closed. -/
def rwR (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) : IProp GF :=
  iprop((∃ w : WDb, wdbOwn B db p sp t0 w ∗ ⌜wdbOK w⌝ ∗ ghostVar B.cls (1 : Qp).half false) ∨
    closedR B db)

/-! ## Lemma statements (U3, U4, U5) -/

theorem Pm_fractional (B : BNs) (db : Loc) : Fractional (Pm (GF := GF) B db) := by
  have fea : ∀ {X : Type} (Φ : X → Qp → IProp GF), (∀ x, Fractional (Φ x)) →
      (∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) → Fractional (fun q => iprop(∃ x, Φ x q)) := by
    intro X Φ hfrac hagree
    refine ⟨fun p q => ⟨?_, ?_⟩⟩
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)
  unfold Pm
  refine fea _ (fun ms => ?_) (fun x y q1 q2 => ?_)
  · have h1 : Fractional (fun q : Qp => ghostVar (GF := GF) B.map q.half.half ms) :=
      ⟨fun p q => by
        rw [Qp_half_add, Qp_half_add]; exact (ghostVar_fractional _ _).fractional _ _⟩
    have hd : DFractional (fun dq => mapFields (GF := GF) db dq ms) := by
      rcases ms with _ | ⟨b, l⟩ <;> simp only [mapFields] <;> infer_instance
    have h2 : Fractional (fun q : Qp => mapFields (GF := GF) db (DFrac.own q.half) ms) :=
      ⟨fun p q => by
        rw [Qp_half_add]
        exact (fractional_of_dfractional (h := hd) _).fractional
          p.half q.half⟩
    have h3 : Fractional (fun q : Qp => ghostVar (GF := GF) B.mtok q ()) :=
      ghostVar_fractional _ _
    infer_instance
  · iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
    icombine H1 H2 gives %H
    ipureintro; exact H.2

theorem Ps_fractional (sp : Loc) : Fractional (Ps (GF := GF) sp) := by
  have fea : ∀ {X : Type} (Φ : X → Qp → IProp GF), (∀ x, Fractional (Φ x)) →
      (∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) → Fractional (fun q => iprop(∃ x, Φ x q)) := by
    intro X Φ hfrac hagree
    refine ⟨fun p q => ⟨?_, ?_⟩⟩
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)
  unfold Ps
  by_cases h : sp = null
  · simp only [h, ite_true]; exact ⟨fun _ _ => emp_sep.symm⟩
  · simp only [h, ite_false]
    refine fea _ (fun s => fractional_of_dfractional
      (fun dq => typedPointsto (GF := GF) sp s dq)) (fun x y q1 q2 => ?_)
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %H
    ipureintro; exact H

/-- The `W` slots are neither tree nor pending slots, nor metas. Used by U3/U4 (`store_publish`,
`store_free` move slots between the store and `W`). -/
theorem wdbOK_partition (w : WDb) (h : wdbOK w) :
    ∀ s ∈ w.W, 2 ≤ s ∧ s ∉ treeSlots w.C ∧ s ∉ pendSlots w.fl := by
  intro s hs
  obtain ⟨h2, -, ht, hp⟩ := (h.2.2.2.1 s).1 hs
  exact ⟨h2, ht, hp⟩

end locks

end bbolt
end EtcdGrove
end Perennial
