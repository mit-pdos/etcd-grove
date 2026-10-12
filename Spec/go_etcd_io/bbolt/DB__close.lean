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

/-- `db.close()` of an opened database whose file is open: the mapping goes (`munmap`), the
file is unlocked (unless read-only) and closed, given back to the file system with its bytes
under its path; the fields are cleared. Over the fields it touches. -/
abbrev DB.close.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (path p : GoString) (ro : Bool)
    (fl : GoInterface) (wa : GoFunc) (dr : GoSlice) (dp : Loc) (ds : w64) (m0 m1 : Loc)
    (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"opened" dbl ↦ true ∗ structFieldRef DB go!"freelist" dbl ↦ fl ∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" dbl) ↦ wa ∗
      structFieldRef DB go!"meta0" dbl ↦ m0 ∗ structFieldRef DB go!"meta1" dbl ↦ m1 ∗
      structFieldRef DB go!"dataref" dbl ↦ dr ∗ structFieldRef DB go!"data" dbl ↦ dp ∗
      structFieldRef DB go!"datasz" dbl ↦ ds ∗
      structFieldRef DB go!"file" dbl ↦ f ∗ structFieldRef DB go!"readOnly" dbl ↦ ro ∗
      structFieldRef DB go!"path" dbl ↦ p ∗
      (⌜f = null ∧ dr = slice.nil⌝ ∨
       (⌜f ≠ null⌝ ∗ fileBytes fd bs ∗
        ((⌜dr = slice.nil⌝ ∗ ∃ (m : Option (Loc × Nat)), fileMap fd m) ∨
         (⌜dr.ptr ≠ null ∧ dr.len = W64 n ∧ dr.cap = W64 n⌝ ∗
          fileMap fd (some (dr.ptr, n)) ∗ mapRange (some (dr.ptr, n)) bs 0 n)) ∗
        osFile f fd ∗ filePath fd path)) }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef DB go!"opened" dbl ↦ false ∗
      structFieldRef DB go!"freelist" dbl ↦ interface.nil ∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" dbl) ↦
        (default : GoFunc) ∗
      structFieldRef DB go!"meta0" dbl ↦ null ∗ structFieldRef DB go!"meta1" dbl ↦ null ∗
      structFieldRef DB go!"dataref" dbl ↦ slice.nil ∗ structFieldRef DB go!"data" dbl ↦ null ∗
      structFieldRef DB go!"datasz" dbl ↦ W64 0 ∗
      structFieldRef DB go!"file" dbl ↦ null ∗ structFieldRef DB go!"readOnly" dbl ↦ ro ∗
      structFieldRef DB go!"path" dbl ↦ go!"" ∗ (⌜f = null⌝ ∨ fsFile path (some bs)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
