/-
`tx.write()` (U10 of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 6): the dirty pages
`tx.pages` (the records' `pm`, their bytes `bufs`) sorted by id and written with
`db.ops.writeAt` (`File.WriteAt`) in chunks of at most `MaxAllocSize - 1` bytes, each page at
`id · 4096`; then `fdatasync` unless `NoSync`; then the one-page buffers zeroed and put back in
the page pool. `tx.pages` is replaced by a fresh empty map first.

The spec is over local resources, as `Tx.writeMeta`'s (the writer side's file and the target
slots, which `Commit` carves out of `wdbLive`'s `W` slots: `wCells`' halves and `wBytes`' bytes):
the slots of every page's extent, whole inside the file and the mapping (`Commit` writes after
`grow`; spill's pages are below the high-water mark, inside the mapping). Afterwards, on success
every slot holds its page's chunk (page-cache bytes and cells, `slotsOwn`); on an error the slots hold some 4096 bytes each (a write may
stop part-way).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteDefs
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.os.File__WriteAt

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

/-- **`tx.write()`** (see the file header): the dirty pages `pm` (`tx.pages`, its buffers holding
`bufs`; every page of `pm` has its buffer, `bufs`' domain is `pm`'s) of a file `om` mapped once at
`b` (`l` bytes), all inside both; the target slots `bufSlots bufs`. Afterwards `tx.pages` is a
fresh empty map, the buffers are gone (the one-page ones to the pool), the file's size and
mappings unchanged, and on success each slot `id + j` of the page `pg` at `id` holds
`pageChunk pg j`, its cells' client halves too (`slotsOwn`, as `store_publish` takes the new slots:
the proof reads them back with `cellsR_agree_bytes` after each `WriteAt`, as `writeMeta` does). -/
abbrev Tx.write.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (sm : Bool) (q : Qp) (dq : DFrac) (pml : Loc)
    (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (wb : Nat → List w8)
    (f : Loc) (fd : w64) (om : OsMeta) (b : Loc) (l : Nat) (dqf dqw : DFrac),
  (∀ id, (pm !! id).isSome = (bufs !! id).isSome) →
  bufsOK bufs (min om.size l / 4096) → om.size < 2 ^ 63 → om.maps = GMap.singleton b l →
  (∀ s ∈ bufSlots bufs, (wb s).length = 4096) →
  {{ K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r sm q ∗
      tx.[Tx, go!"db"] ↦{dq} K.db ∗ tx.[Tx, go!"pages"] ↦ pml ∗ pml ↦$ pm ∗
      ([∗map] id ↦ pl ∈ pm, ∃ bs, ⌜bufs !! id = some bs⌝ ∗ bytesPointsto pl (DFrac.own 1) bs) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗
      osMeta K.p (DFrac.own 1) (some om) ∗ wrSlots b K.p (bufSlots bufs) wb }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
  {{ (err : GoInterface), RET #err; statsTok r sm q ∗ tx.[Tx, go!"db"] ↦{dq} K.db ∗
      (∃ pml' : Loc, tx.[Tx, go!"pages"] ↦ pml' ∗ pml' ↦$ (∅ : GMap w64 Loc)) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨K.p, true, true⟩ ∗
      (∃ om' : OsMeta, osMeta K.p (DFrac.own 1) (some om') ∗
        ⌜om'.size = om.size ∧ om'.maps = om.maps⌝) ∗
      ∃ wb' : Nat → List w8, ⌜∀ s ∈ bufSlots bufs, (wb' s).length = 4096⌝ ∗
        ((⌜err = interface.nil⌝ ∗ ⌜∀ id pg, bufs !! id = some pg → ∀ j < 1 + pageOverflow pg,
            wb' (id.toNat + j) = pageChunk pg j⌝ ∗
            slotsOwn (some (b, l) : MapSt) K.p (bufSlots bufs) wb') ∨
         (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ wrSlots b K.p (bufSlots bufs) wb')) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- Not yet (U10b): the map-to-slice loop, `sort.Sort` (`Pages`' `Len`/`Less`/`Swap`, a
permutation suffices: the extents are disjoint), the chunk loop over `WriteAt`, `fdatasync`, the
zeroing loop and `pagePool.Put`. -/
theorem Tx.write.wp_proof (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncWrite.spec (GF := GF) (hG := hG)) :
    Tx.write.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
