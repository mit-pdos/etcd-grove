/-
`db.loadFreelist()` at `Open` (U11e; design §3.11 "Open", steps 2-3): its own spec, which takes
`Open/Core.open_core`'s inputs before the carving (`Open/Carve.open_carve`) and performs the core
phase itself, where the code needs it: in the synced case after `Interface.Read` (which reads the
freelist page's bytes, writer-side `W` slots whose cells the core keeps only as `∃ vf`), in the
unsynced case before `freepages` (a read transaction on the core and the spare reader pair). The
loaded freelist is published under `metalock`, its free count under `statlock`; the post is
`Open/Core.open_writer`'s inputs but `rwlock`, with `wdbOK` of the writer side.

An internal spec of this unit (not in `Spec/`: `loadFreelist` is called only by `Open` here).
-/
module

public import Proof.go_etcd_io.bbolt.Open.LoadFL
public import Proof.go_etcd_io.bbolt.Open.Carve
public import Proof.go_etcd_io.bbolt.Open.OnceOwn
public import Spec.go_etcd_io.bbolt.newFreelist
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.DB__freepages
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Read
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__FreeCount
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The slots' bytes of the opened file `xs`. -/
def openWb (xs : List (w8 × Bool)) : Nat → List w8 :=
  fun s => bytesAt (xs.map Prod.fst) (4096 * s) 4096

/-- The pure facts `loadFreelist` needs of the opened file `xs` (`fileHolds_decode`'s, the
mapping `(b, L)`'s, `Open`'s namespace and database). -/
def lfOK (N : Namespace) (db : Loc) (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta)
    (xs : List (w8 × Bool)) : Prop :=
  fileImage (xs.map Prod.fst) C ∧ C.metaOk ∧ treeOK C ∧ flFileOK (xs.map Prod.fst) C ∧
    C.hwm * 4096 ≤ xs.length ∧ 8192 ≤ xs.length ∧ xs.length = m.size ∧ m.size ≤ L ∧
    m.size < 2 ^ 63 ∧ m.maps = GMap.singleton b L ∧ 1 ≤ C.txid ∧ C.txid < 2 ^ 62 ∧
    (↑N : CoPset) ## ↑osN ∧ db ≠ null

/-- **What `loadFreelist` takes at `Open`**: `open_core`'s inputs, the mapping's client halves
not yet carved (the file's bytes at a half, the rest any cells). -/
def lfPre (db sp f : Loc) (fd : w64) (p : GoString) (b : Loc) (L : Nat) (m : OsMeta)
    (xs : List (w8 × Bool)) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed db sp ∗
      db.[DB, go!"metalock"] ↦ (zero_val sync.Mutex) ∗
      db.[DB, go!"mmaplock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"statlock"] ↦ (zero_val sync.RWMutex) ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"rwtx"] ↦ null ∗ db.[DB, go!"file"] ↦ f ∗ db.[DB, go!"path"] ↦ p ∗
      db.[DB, go!"datasz"] ↦ W64 (L : Int) ∗
      mapFields db (DFrac.own 1) (some (b, L)) ∗
      osMeta p (DFrac.own 1) (some m) ∗ fileOwn f fd p (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p, true, true⟩ ∗ Ps sp 1 ∗
      osBytes p 0 (DFrac.own 1) xs ∗
      bytesPointsto b (DFrac.own (1 : Qp).half) (xs.map Prod.fst) ∗
      ∃ vf, cellsR b xs.length (L - xs.length) vf)

/-- The writer side after `loadFreelist`. -/
def lfW (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List (w8 × Bool)) (f : Loc)
    (fd : w64) (fl : FLPg) (fli : GoInterface) : WDb :=
  { openW C b L m (openWb xs) f fd with fl := fl, fli := fli }

/-- **What `loadFreelist` gives at `Open`**: `open_writer`'s inputs but `rwlock`. -/
def lfPost (N : Namespace) (db sp f : Loc) (fd : w64) (p : GoString) (C : CommitSt) (b : Loc)
    (L : Nat) (m : OsMeta) (xs : List (w8 × Bool)) : IProp GF :=
  iprop(∃ (B : BNs) (fl : FLPg) (fli : GoInterface),
    isBoltCoreP B N db p sp C.txid ∗
    threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗
    wdbCore B db p (lfW C b L m xs f fd fl fli) ∗ ghostVar B.st (1 : Qp).half.half (treeData C) ∗
    flPgOwn fli fl ∗ rdPair B db sp ∗ ghostVar B.cls (1 : Qp).half false ∗
    boltStateDef B 1 (treeData C) ∗ ⌜wdbOK (lfW C b L m xs f fd fl fli)⌝)

/-- **`db.loadFreelist()` at `Open`**. -/
abbrev DB.loadFreelist.spec_open : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] (N : Namespace) (db sp f : Loc) (fd : w64) (p : GoString)
    (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (xs : List (w8 × Bool)),
  lfOK N db C b L m xs →
  {{ lfPre (GF := GF) db sp f fd p b L m xs ∗
      db.[DB, go!"freelistLoad"] ↦ (zero_val sync.Once) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"loadFreelist")) (Val #()))
  {{ RET #(); lfPost N db sp f fd p C b L m xs }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The current meta's `Freelist()` when it names the page `g`. -/
theorem wp_curMeta_Freelist (hFreelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (b : Loc) (l : Nat) (C : CommitSt) (q : Qp) (hok : C.metaOk) (g : Nat)
    (hg : C.flpg = some g) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
        metaCellsQ q (some (b, l) : MapSt) C }}
      (App (Val ((b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) @!!
        go.GoType.PointerType Meta.ty @!! go!"Freelist")) (Val #()))
    {{ RET #(W64 (g : Int)); metaCellsQ q (some (b, l) : MapSt) C }} := by
  wp_start_folded as Hmc
  obtain ⟨hl0, hl1, -, -, -, -, ⟨-, -, -, hfl⟩, -⟩ := hok
  have hval : ∀ v : Meta, metaFlpg v = C.flpg → v.freelist' = W64 (g : Int) := by
    intro v hv
    rw [hg] at hv
    unfold metaFlpg at hv
    split at hv
    · cases hv
    · cases hv
      apply BitVec.eq_of_toNat_eq
      have := BitVec.isLt v.freelist'
      simp
  simp only [metaCellsQ]
  icases Hmc with ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · unfold CommitSt.slot at hfl
    simp only [hT, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    generalize metaOf C.m0 = v0 at hfl ⊢
    wp_apply hFreelist _ v0 (DFrac.own q) $$ [M0] as M0
    · iframe
    rw [hval _ hfl]
    ihave H0 := C0 $$ M0
    iapply HΦ; iframe
  · unfold CommitSt.slot at hfl
    simp only [show C.txid % 2 ≠ 0 by omega, ↓reduceIte] at hfl
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    generalize metaOf C.m1 = v1 at hfl ⊢
    wp_apply hFreelist _ v1 (DFrac.own q) $$ [M1] as M1
    · iframe
    rw [hval _ hfl]
    ihave H1 := C1 $$ M1
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
