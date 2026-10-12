module
public import Spec.go_etcd_io.bbolt.DB__fileSize
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Proof.runtime.GOOS

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

variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

/-- `db.grow(sz)` (no `Mlock`, Linux): the file grows to `growSize(datasz, sz)` bytes if it is
shorter than `sz` (unless `NoGrowSync` or read-only), the mapping's new cells (if it covers
them) given back; on an error, it may or may not have. The file must not be longer than the
mapping (`datasz`), nor `sz` (bbolt's callers remap first): `growSize` may return `datasz`.
Over the fields it reads. -/
abbrev DB.grow.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (m : Option (Loc × Nat)) (dq : DFrac)
    (lg : GoInterface) (dl : Loc) (ps dsz al : w64) (ngs ro : Bool) (sz : w64),
  dbl ≠ null → bs.length < 2 ^ 62 → uint.Z ps < 2 ^ 32 →
  0 ≤ sint.Z sz → 0 ≤ sint.Z dsz → 0 ≤ sint.Z al → sint.Z sz + sint.Z al < 2 ^ 62 →
  sint.Z dsz < 2 ^ 62 → bs.length ≤ sint.Z dsz → sint.Z sz ≤ sint.Z dsz → (lg = interface.nil ∨ lg = discardIface dl) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"logger" dbl ↦{dq} lg ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗
      structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      structFieldRef DB go!"datasz" dbl ↦{dq} dsz ∗
      structFieldRef DB go!"AllocSize" dbl ↦{dq} al ∗
      structFieldRef DB go!"NoGrowSync" dbl ↦{dq} ngs ∗
      structFieldRef DB go!"readOnly" dbl ↦{dq} ro ∗
      structFieldRef DB go!"Mlock" dbl ↦{dq} false ∗
      (globalAddr discardLogger ↦□ dl : IProp GF) ∗ defaultLoggerOK dl ∗
      osFile f fd ∗ fileBytes fd bs ∗ fileMap fd m }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"grow")) (Val #sz))
  {{ (err : GoInterface), RET #err; ∃ (bs' : List w8),
      structFieldRef DB go!"logger" dbl ↦{dq} lg ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗
      structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      structFieldRef DB go!"datasz" dbl ↦{dq} dsz ∗
      structFieldRef DB go!"AllocSize" dbl ↦{dq} al ∗
      structFieldRef DB go!"NoGrowSync" dbl ↦{dq} ngs ∗
      structFieldRef DB go!"readOnly" dbl ↦{dq} ro ∗
      structFieldRef DB go!"Mlock" dbl ↦{dq} false ∗
      fileBytes fd bs' ∗ fileMap fd m ∗ mapRange m bs' bs.length bs'.length ∗
      ⌜(bs' = bs ∨ ∃ n, bs' = truncBytes bs n ∧ bs.length ≤ n) ∧
        (err = interface.nil → sint.Z sz ≤ bs'.length ∨ ngs = true ∨ ro = true)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
