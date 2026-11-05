/-
`Tx.write_ext` (bbolt, internal; maintainer 12, item 3 of `notes/bbolt-proof-plan.md`): `tx.write()`
with dirty pages past the end of the file. Under `NoGrowSync`, `DB.grow` does not truncate, so the
dirty pages may lie past the file's end (inside the mapping); `WriteAt` extends the file (OsFs's
`pwrite`, `os.File.WriteAt.spec`: the zero gap past the old end, then the data). `Tx.write.spec`
(`Proof/go_etcd_io/bbolt/Tx__write.lean`, proved) is the case of pages inside the file. Proof:
`Proof/go_etcd_io/bbolt/Tx__write_ext.lean` (`Commit/WriteExtRun.Tx.write_ext_gen`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WSlots

@[expose] public section

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

/-- **`tx.write()`, the dirty pages anywhere in the mapping** (`Tx.write.spec` but the pages need
not lie inside the file). The target slots are the pages' `bufSlots bufs` and the tail `T`: every
slot of the mapping not wholly inside the file is one of them (a write past the end fills the gap
before it with zeros, which needs the gap's cells: `os.File.WriteAt.spec`'s `mcellsAny`), all as
`wrSlotsSz` (`Inv/WSlots`) at the file's size, a slot across the file's end holding at least its
part inside the file (maintainer 13: `wdbOK`'s partial-page clause, D-J). Afterwards the file is no smaller and ends within the mapping or
where it ended (`om.size ≤ om'.size ≤ max om.size l`), a tail slot inside the old file keeps its
bytes, and a slot across the new end holds at least its part inside the file (on an error too: the
slots the write touched hold some whole page's bytes); on success every page slot is inside the new file, holding its chunk (`slotsOwn`, as
`store_publish` takes it) and the tail is `wrSlotsSz` at the new size; on an error all the slots
are, with whatever bytes the write left. On success the success branch also restates the
straddling-slot fact (kept there for its consumers) and says that the file either kept its size or
ends on a page boundary (it grew by whole pages); not on an error, where `WriteAt` may have written
part of a chunk. -/
abbrev Tx.write_ext.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (sm : Bool) (q : Qp) (dq : DFrac) (pml : Loc)
    (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (T : List Nat) (wb : Nat → List w8)
    (f : Loc) (fd : w64) (om : OsMeta) (b : Loc) (l : Nat) (dqf dqw : DFrac),
  (∀ id, (pm !! id).isSome = (bufs !! id).isSome) →
  bufsOK bufs (l / 4096) → om.size < 2 ^ 63 → l < 2 ^ 63 → om.maps = GMap.singleton b l →
  (bufSlots bufs ++ T).Nodup → (∀ s ∈ T, s < l / 4096) →
  (∀ s, s < l / 4096 → om.size < 4096 * (s + 1) → s ∈ bufSlots bufs ∨ s ∈ T) →
  (∀ s ∈ bufSlots bufs ++ T, 4096 * (s + 1) ≤ om.size → (wb s).length = 4096) →
  (∀ s ∈ bufSlots bufs ++ T, 4096 * s < om.size → om.size < 4096 * (s + 1) →
    om.size - 4096 * s ≤ (wb s).length) →
  {{ K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r sm q ∗
      tx.[Tx, go!"db"] ↦{dq} K.db ∗ tx.[Tx, go!"pages"] ↦ pml ∗ pml ↦$ pm ∗
      ([∗map] id ↦ pl ∈ pm, ∃ bs, ⌜bufs !! id = some bs⌝ ∗ bytesPointsto pl (DFrac.own 1) bs) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗
      osMeta K.p (DFrac.own 1) (some om) ∗ wrSlotsSz b K.p (bufSlots bufs ++ T) wb om.size }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
  {{ (err : GoInterface), RET #err; statsTok r sm q ∗ tx.[Tx, go!"db"] ↦{dq} K.db ∗
      (∃ pml' : Loc, tx.[Tx, go!"pages"] ↦ pml' ∗ pml' ↦$ (∅ : GMap w64 Loc)) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗
      ∃ (om' : OsMeta) (wb' : Nat → List w8), osMeta K.p (DFrac.own 1) (some om') ∗
        ⌜om.size ≤ om'.size ∧ om'.size ≤ max om.size l ∧ om'.maps = om.maps ∧
          (∀ s ∈ bufSlots bufs ++ T, 4096 * (s + 1) ≤ om'.size → (wb' s).length = 4096) ∧
          (∀ s ∈ T, 4096 * (s + 1) ≤ om.size → wb' s = wb s) ∧
          (∀ s ∈ bufSlots bufs ++ T, 4096 * s < om'.size → om'.size < 4096 * (s + 1) →
            om'.size - 4096 * s ≤ (wb' s).length)⌝ ∗
        ((⌜err = interface.nil⌝ ∗ ⌜(∀ s ∈ bufSlots bufs, 4096 * (s + 1) ≤ om'.size) ∧
            (∀ id pg, bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
              wb' (id.toNat + j) = pageChunk pg j) ∧
            (∀ s ∈ bufSlots bufs ++ T, 4096 * s < om'.size → om'.size < 4096 * (s + 1) →
              om'.size - 4096 * s ≤ (wb' s).length) ∧
            (om'.size = om.size ∨ om'.size % 4096 = 0)⌝ ∗
            slotsOwn (some (b, l) : MapSt) K.p (bufSlots bufs) wb' ∗ wrSlotsSz b K.p T wb' om'.size) ∨
         (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
            wrSlotsSz b K.p (bufSlots bufs ++ T) wb' om'.size)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
