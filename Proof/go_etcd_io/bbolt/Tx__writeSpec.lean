/-
`Tx.write.spec`, out of `Tx__write.lean`'s proof so that `Commit/WriteExtRun.lean` imports it without the
proof (import tiers, 2026-11-18).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WriteDefs
public import Proof.go_etcd_io.bbolt.Commit.WriteLoop
public import Proof.go_etcd_io.bbolt.Commit.PagesSort
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Proof.go_etcd_io.bbolt.Mmap.LoggerDefs
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.go_etcd_io.bbolt.internal.common.Page__Overflow
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Perennial.Proof.sync.Link
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.os.File__WriteAt

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
      fileOwn f fd K.p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd K.p.ino) ∗
      osMeta K.p.ino (DFrac.own 1) om ∗ wrSlots b K.p (bufSlots bufs) wb }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"write")) (Val #()))
  {{ (err : GoInterface), RET #err; statsTok r sm q ∗ tx.[Tx, go!"db"] ↦{dq} K.db ∗
      (∃ pml' : Loc, tx.[Tx, go!"pages"] ↦ pml' ∗ pml' ↦$ (∅ : GMap w64 Loc)) ∗
      K.db.[DB, go!"file"] ↦{dqf} f ∗
      (K.db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      fileOwn f fd K.p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd K.p.ino) ∗
      (∃ om' : OsMeta, osMeta K.p.ino (DFrac.own 1) om' ∗
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
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
end proof

end bbolt
end EtcdGrove
end Perennial
