module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel
public import Proof.os.FileInfoAlias

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

/-- `db.fileSize()`: the file's size, if `Stat` works and it holds two pages; otherwise an
error. Over the fields it reads. -/
abbrev DB.fileSize.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (ps : w64) (dq dqs : DFrac),
  bs.length < 2 ^ 62 → uint.Z ps < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ structFieldRef DB go!"file" dbl ↦{dq} f ∗
      structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗ osFile f fd ∗ fileBytes fd bs }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"fileSize")) (Val #()))
  {{ (sz : w64) (err : GoInterface), RET (PairV #sz #err);
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      fileBytes fd bs ∗
      ⌜(err = interface.nil → sz = W64 bs.length ∧ 2 * uint.Z ps ≤ bs.length) ∧
        (err = interface.nil ∨ IsNewErr err)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
