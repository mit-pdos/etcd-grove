module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel
public import Proof.go_etcd_io.bbolt.ErrShape

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `mmap(db, sz)`: maps the first `sz` bytes of the file read-only (`MAP_SHARED`), the
caller getting its half of the mapped cells (those inside the file); `db.dataref` is the
mapping's slice, `db.data` its start and `db.datasz` its size. If `Mmap` fails nothing
changes; if `Madvise` fails (other than `ENOSYS`), the fields are unchanged but the mapping
stays (bbolt loses it). Over the fields it touches. -/
abbrev mmap.spec : Prop :=
  ∀ (dbl f : Loc) (fl : w64) (dq : DFrac) (dr : GoSlice) (dp : Loc) (ds : w64) (fd : w64)
    (bs : List w8) (sz : w64),
  0 < sint.Z sz →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"file" dbl ↦{dq} f ∗
      structFieldRef DB go!"MmapFlags" dbl ↦{dq} fl ∗ structFieldRef DB go!"dataref" dbl ↦ dr ∗ structFieldRef DB go!"data" dbl ↦ dp ∗
      structFieldRef DB go!"datasz" dbl ↦ ds ∗ osFile f fd ∗ fileBytes fd bs ∗ fileMap fd none }}
    (App (App (Val #(functions mmap [])) (Val #dbl)) (Val #sz))
  {{ (err : GoInterface), RET #err;
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"MmapFlags" dbl ↦{dq} fl ∗ fileBytes fd bs ∗
      ((⌜err ≠ interface.nil ∧ errWF err⌝ ∗ structFieldRef DB go!"dataref" dbl ↦ dr ∗ structFieldRef DB go!"data" dbl ↦ dp ∗
          structFieldRef DB go!"datasz" dbl ↦ ds ∗
          (fileMap fd none ∨ ∃ (p : Loc), fileMap fd (some (p, sint.nat sz)) ∗
            mapRange (some (p, sint.nat sz)) bs 0 (sint.nat sz))) ∨
       (∃ (b : GoSlice), ⌜err = interface.nil ∧ b.len = sz ∧ b.cap = sz ∧ b.ptr.locCar ≠ 0⌝ ∗
          structFieldRef DB go!"dataref" dbl ↦ b ∗ structFieldRef DB go!"data" dbl ↦ b.ptr ∗ structFieldRef DB go!"datasz" dbl ↦ sz ∗
          fileMap fd (some (b.ptr, sint.nat sz)) ∗
          mapRange (some (b.ptr, sint.nat sz)) bs 0 (sint.nat sz))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
