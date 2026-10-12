module
public import Proof.go_etcd_io.bbolt.DBPred
public import Spec.go_etcd_io.bbolt.DB__mmapSize
public import Proof.os.FileInfoAlias
public import Proof.runtime.GOOS
public import Proof.go_etcd_io.bbolt.ErrShape
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

/-- The two metas of a file of pages of `ps` bytes (64 bytes after each of the first two
pages' headers): `v0`, `v1`, one of them valid. -/
def metasOK (bs : List w8) (ps : Nat) (v0 v1 : internal.common.Meta) : Prop :=
  ((slotAt bs ps 0).drop 16).take 64 = metaBytes v0 ∧
  ((slotAt bs ps 1).drop 16).take 64 = metaBytes v1 ∧ (metaValid v0 ∨ metaValid v1)

/-- `db.mmap(minsz)` (no `Mlock`, Linux): maps the file anew, `mmapSize` of the larger of its
size and `minsz` bytes, and points `meta0`, `meta1` at its two metas (one valid).

It first takes `mmaplock` for writing: the read locks of open readers (their `mmapTok`
tokens, `M`) are released by then, so `M` is empty (in sequential use, an open reader makes
it wait forever). A writer open (`rwtx`) is dereferenced (`WR` to `WR'`, the hypothesis on
`tx.root.dereference()`) before the old mapping goes; the caller lends that mapping's cells
(`mapRange`, and the `data` field) once no reader holds them (the wand, from `M = ∅` and
`WR'`), keeping `K`.

On an error before the dereference nothing changed (`WR`, the wand); after it, the mapping
is gone or lost (`fileMap fd m'`, the fields cleared). -/
abbrev DB.mmap.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (lg : GoInterface) (dl : Loc) (ps ms mf : w64)
    (rw : Loc) (dq : DFrac) (dr : GoSlice) (dp : Loc) (ds : w64) (m0 m1 : Loc)
    (m : Option (Loc × Nat)) (n : Nat) (γ : GName) (M : GMap Nat Reader) (WR WR' K : IProp GF)
    (minsz : w64),
  dbl ≠ null → bs.length < 2 ^ 62 → 80 ≤ uint.Z ps → uint.Z ps < 2 ^ 32 →
  0 ≤ sint.Z minsz → sint.Z minsz < 2 ^ 62 → (lg = interface.nil ∨ lg = discardIface dl) →
  ((dr = slice.nil ∧ m = none) ∨
    (dr.ptr ≠ null ∧ dr.len = W64 n ∧ dr.cap = W64 n ∧ m = some (dr.ptr, n))) →
  (rw = null → (WR ⊢ WR')) →
  (rw ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ WR }}
      (App (Val (structFieldRef Tx go!"root" rw @!! go.GoType.PointerType Bucket.ty @!! go!"dereference"))
        (Val #()))
    {{ RET #(); WR' }}) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"logger" dbl ↦□ lg ∗ (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      defaultLoggerOK dl ∗ structFieldRef DB go!"pageSize" dbl ↦□ ps ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"MaxSize" dbl ↦{dq} ms ∗
      structFieldRef DB go!"Mlock" dbl ↦□ false ∗ structFieldRef DB go!"rwtx" dbl ↦{dq} rw ∗
      structFieldRef DB go!"MmapFlags" dbl ↦{dq} mf ∗
      structFieldRef DB go!"dataref" dbl ↦ dr ∗ structFieldRef DB go!"datasz" dbl ↦ ds ∗
      structFieldRef DB go!"meta0" dbl ↦ m0 ∗ structFieldRef DB go!"meta1" dbl ↦ m1 ∗
      osFile f fd ∗ fileBytes fd bs ∗ fileMap fd m ∗
      sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ) ∗
      ([∗map] _k ↦ _r ∈ M, mmapTok γ sync.rfrac) ∗ WR ∗
      (⌜M = ∅⌝ -∗ WR' -∗
        structFieldRef DB go!"data" dbl ↦ dp ∗ mapRange m bs 0 n ∗ K) }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"mmap")) (Val #minsz))
  {{ (err : GoInterface), RET #err;
      ⌜M = ∅⌝ ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"MaxSize" dbl ↦{dq} ms ∗
      structFieldRef DB go!"Mlock" dbl ↦□ false ∗ structFieldRef DB go!"rwtx" dbl ↦{dq} rw ∗
      structFieldRef DB go!"MmapFlags" dbl ↦{dq} mf ∗ fileBytes fd bs ∗
      sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ) ∗
      ((⌜err ≠ interface.nil ∧ errWF err⌝ ∗ WR ∗
          (⌜M = ∅⌝ -∗ WR' -∗
            structFieldRef DB go!"data" dbl ↦ dp ∗ mapRange m bs 0 n ∗ K) ∗
          structFieldRef DB go!"dataref" dbl ↦ dr ∗ structFieldRef DB go!"datasz" dbl ↦ ds ∗
          structFieldRef DB go!"meta0" dbl ↦ m0 ∗ structFieldRef DB go!"meta1" dbl ↦ m1 ∗
          fileMap fd m) ∨
       (⌜err ≠ interface.nil ∧ errWF err⌝ ∗ K ∗ ∃ (dp' : Loc) (ds' : w64) (m0' m1' : Loc)
          (m' : Option (Loc × Nat)) (n' : Nat),
          structFieldRef DB go!"dataref" dbl ↦ slice.nil ∗ structFieldRef DB go!"data" dbl ↦ dp' ∗
          structFieldRef DB go!"datasz" dbl ↦ ds' ∗
          structFieldRef DB go!"meta0" dbl ↦ m0' ∗ structFieldRef DB go!"meta1" dbl ↦ m1' ∗
          fileMap fd m' ∗ mapRange m' bs 0 n') ∨
       (⌜err = interface.nil⌝ ∗ K ∗ ∃ (b : GoSlice) (sz : w64) (v0 v1 : internal.common.Meta),
          ⌜b.len = sz ∧ b.cap = sz ∧ b.ptr.locCar ≠ 0 ∧
            mmapSizeOf (max (bs.length : Int) (sint.Z minsz)) (uint.Z ps) = some (sint.Z sz) ∧
            metasOK bs (uint.nat ps) v0 v1⌝ ∗
          structFieldRef DB go!"dataref" dbl ↦ b ∗ structFieldRef DB go!"data" dbl ↦ b.ptr ∗
          structFieldRef DB go!"datasz" dbl ↦ sz ∗
          structFieldRef DB go!"meta0" dbl ↦ (b.ptr +ₗ 16) ∗
          structFieldRef DB go!"meta1" dbl ↦ (b.ptr +ₗ (uint.Z ps + 16)) ∗
          fileMap fd (some (b.ptr, sint.nat sz)) ∗
          mapRange (some (b.ptr, sint.nat sz)) bs 0 (sint.nat sz))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
