/-
`commitStep`, `Tx.writeMeta.spec` and the lemmas of `Tx__writeMeta.lean`'s proof, in a module of their
own so that the commit's definitions (`Commit/Step.lean`) import them without the proof (import
tiers, 2026-11-18).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Commit.MetaBuf
public import Proof.go_etcd_io.bbolt.Mmap.LoggerDefs
public import Proof.go_etcd_io.bbolt.Mmap.Cells
public import Proof.go_etcd_io.bbolt.Mmap.RemapCells
public import Proof.go_etcd_io.bbolt.Commit.MetaPage
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Write
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.os.File__WriteAt
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link
public import Proof.ReceiptTactics
public import Proof.go_etcd_io.bbolt.Mmap.Infra

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The commit step `writeMeta` runs under `metalock` right after the meta page's `WriteAt`
(slot `s`, the mapping's base `b`): from `metalock`'s resource, the slot's page-cache bytes
(whole) and its cells' client halves (as bytes at ½), and, given them back as the write left
them (`j` bytes written, all or nothing) and a time receipt (of a step under `metalock`, for
the writer side's receipts), `metalock`'s resource and `Ψ j`. -/
def commitStep (K : BC) (s : Nat) (b : Loc) (buf : List w8) (Ψ : Nat → IProp GF) : IProp GF :=
  iprop(metaR K.B K.db K.p ={⊤}=∗ ∃ (xs : List ByteG) (old : List w8),
    osBytes K.p.ino (4096 * s) (DFrac.own 1) xs ∗ ⌜xs.length = 4096 ∧ old.length = 4096⌝ ∗
    bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) old ∗
    ∀ (j : Nat) (ys : List ByteG),
      ⌜(j = 0 ∨ j = 4096) ∧ ys.map Prod.fst = (if j = 0 then xs.map Prod.fst else buf)⌝ -∗
      osBytes K.p.ino (4096 * s) (DFrac.own 1) ys -∗
      bytesPointsto (b +ₗ ((4096 * s : Nat) : Int)) (DFrac.own (1 : Qp).half) (ys.map Prod.fst) -∗
      receipt 1 ={⊤}=∗ metaR K.B K.db K.p ∗ Ψ j)

/-- **`tx.writeMeta()`** (see the file header): the meta `mv` (as `Meta.Write` needs it) written
at slot `mv.txid % 2` of a file of at least two pages mapped once at `b` (at least two pages);
the commit step `commitStep` runs under `metalock`. Afterwards the meta is summed, the file's
size and mappings are unchanged, and `Ψ j` holds for the bytes written `j` (all of them on
success). -/
abbrev Tx.writeMeta.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (sm : Bool) (q : Qp) (dq : DFrac) (mp : Loc) (mv : Meta)
    (f : Loc) (fd : w64) (om : OsMeta) (b : Loc) (l : Nat) (dqf dqw : DFrac)
    (Ψ : Nat → IProp GF),
  uint.Z mv.root'.root' < uint.Z mv.pgid' →
  (uint.Z mv.freelist' < uint.Z mv.pgid' ∨ mv.freelist'.toNat = pgidNoFreelist) →
  0 < mp.addr → 8192 ≤ om.size → om.maps = GMap.singleton b l → 8192 ≤ l →
  {{ K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r sm q ∗
      tx.[Tx, go!"db"] ↦{dq} K.db ∗ tx.[Tx, go!"meta"] ↦{dq} mp ∗ mp ↦ mv ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd K.p.ino) ∗
      osMeta K.p.ino (DFrac.own 1) om ∗
      commitStep K (mv.txid'.toNat % 2) b (metaBuf mv) Ψ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"writeMeta")) (Val #()))
  {{ (err : GoInterface), RET #err; statsTok r sm q ∗
      tx.[Tx, go!"db"] ↦{dq} K.db ∗ tx.[Tx, go!"meta"] ↦{dq} mp ∗ mp ↦ metaSummed mv ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd K.p.ino) ∗
      (∃ om' : OsMeta, osMeta K.p.ino (DFrac.own 1) om' ∗
        ⌜om'.size = om.size ∧ om'.maps = om.maps⌝) ∗
      ∃ j : Nat, Ψ j ∗ ⌜(j = 0 ∨ j = 4096) ∧ (err = interface.nil → j = 4096)⌝ ∗
        (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err) }}

end spec
section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
omit hos sem package_sem in
/-- The client halves of a slot's cells, as `WriteAt`'s `mcellsAny` over the one mapping. -/
theorem wm_cells_of_bytes (b : Loc) (l lo : Nat) (old : List w8) (hl : lo + 4096 ≤ l)
    (hlen : old.length = 4096) :
    bytesPointsto (GF := GF) (b +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) old ⊢
      mcellsAny (GF := GF) {[b := l]} lo (lo + 4096) := by
  unfold mcellsAny
  refine Entails.trans ?_ BigSepM.bigSepM_singleton.2
  rw [show min lo l = lo by omega, show min (lo + 4096) l - lo = old.length by omega]
  exact (bytes_cellsR b old lo).trans (exists_intro (Ψ := fun vf => cellsR b lo old.length vf) _)

omit [GooseSemantics] go_gctx hos sem package_sem in
theorem wm_cells_any (b : Loc) (l lo : Nat) (hl : lo + 4096 ≤ l) :
    mcellsAny (GF := GF) {[b := l]} lo (lo + 4096) ⊢ ∃ vf, cellsR (GF := GF) b lo 4096 vf := by
  unfold mcellsAny
  refine BigSepM.bigSepM_singleton.1.trans ?_
  rw [show min lo l = lo by omega, show min (lo + 4096) l - lo = 4096 by omega]

omit [GooseSemantics] hos in
/-- A `Pgid` is formatted as its integer (a named `uint64` without methods). -/
theorem pgid_argWf (v : w64) : _root_.Perennial.fmt.ArgWf (interface.mk Pgid.ty #v) := by
  have hu : underlying Pgid.ty = go.uint64 := go.IsUnderlying.is_underlying
  have hni : ¬ _root_.Perennial.fmt.IsIntType Pgid.ty := by
    simp [_root_.Perennial.fmt.IsIntType, Pgid.ty, go.int, go.int64, go.int32, go.int16, go.int8,
      go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
  have hint : _root_.Perennial.fmt.IsIntType (underlying Pgid.ty) := by
    rw [hu]; simp [_root_.Perennial.fmt.IsIntType]
  have hnf := _root_.Perennial.fmt.NoFmtMethods.of_methodSetIs_nil Pgid.ty
  refine ⟨fun h => ?_, fun _ => ⟨uint.Z v, .named _ _ _ hni hint hnf ?_⟩, Or.inr (Or.inl (Or.inr ⟨hint, hnf⟩))⟩
  · simp [Pgid.ty, go.string] at h
  · show _root_.Perennial.fmt.IntArgValue (interface.mk (underlying Pgid.ty) #v) (uint.Z v)
    rw [hu]; exact .uint64 v

end proof

end bbolt
end EtcdGrove
end Perennial
