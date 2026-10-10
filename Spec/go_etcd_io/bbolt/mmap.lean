module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel

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
changes; if `Madvise` fails (other than `ENOSYS`), `db` is unchanged but the mapping stays
(bbolt loses it). -/
abbrev mmap.spec : Prop :=
  ∀ (dbl : Loc) (d : DB) (fd : w64) (bs : List w8) (sz : w64),
  0 < sint.Z sz →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbl ↦ d ∗ osFile d.file' fd ∗ fileBytes fd bs ∗ fileMap fd none }}
    (App (App (Val #(functions mmap [])) (Val #dbl)) (Val #sz))
  {{ (err : GoInterface), RET #err;
      fileBytes fd bs ∗
      ((⌜err ≠ interface.nil⌝ ∗ dbl ↦ d ∗
          (fileMap fd none ∨ ∃ (p : Loc), fileMap fd (some (p, sint.nat sz)) ∗
            mapRange (some (p, sint.nat sz)) bs 0 (sint.nat sz))) ∨
       (∃ (b : GoSlice), ⌜err = interface.nil ∧ b.len = sz ∧ b.cap = sz ∧ b.ptr.locCar ≠ 0⌝ ∗
          dbl ↦ ({ d with dataref' := b, data' := b.ptr, datasz' := sz } : DB) ∗
          fileMap fd (some (b.ptr, sint.nat sz)) ∗
          mapRange (some (b.ptr, sint.nat sz)) bs 0 (sint.nat sz))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
