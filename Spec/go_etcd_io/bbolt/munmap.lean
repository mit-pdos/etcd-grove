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

/-- `munmap(db)`: if the file is mapped (`db.dataref`, as `mmap` set it), the mapping goes,
with the caller's half of its cells, and `dataref`, `data`, `datasz` are cleared. Over the
fields it touches. -/
abbrev munmap.spec : Prop :=
  ∀ (dbl : Loc) (dr : GoSlice) (dp : Loc) (ds : w64) (fd : w64) (bs : List w8) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"dataref" dbl ↦ dr ∗ structFieldRef DB go!"data" dbl ↦ dp ∗ structFieldRef DB go!"datasz" dbl ↦ ds ∗
      fileBytes fd bs ∗
      ((⌜dr = slice.nil⌝ ∗ fileMap fd none) ∨
       (⌜dr.ptr ≠ null ∧ dr.len = W64 n ∧ dr.cap = W64 n⌝ ∗
        fileMap fd (some (dr.ptr, n)) ∗ mapRange (some (dr.ptr, n)) bs 0 n)) }}
    (App (Val #(functions munmap [])) (Val #dbl))
  {{ RET #interface.nil;
      structFieldRef DB go!"dataref" dbl ↦ slice.nil ∗
      structFieldRef DB go!"data" dbl ↦ (if dr = slice.nil then dp else null) ∗
      structFieldRef DB go!"datasz" dbl ↦ (if dr = slice.nil then ds else W64 0) ∗
      fileBytes fd bs ∗ fileMap fd none }}

end spec

end bbolt
end EtcdGrove
end Perennial
