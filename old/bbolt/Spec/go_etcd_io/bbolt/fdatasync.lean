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

/-- `fdatasync(db)`: `Fdatasync` of the file's descriptor (no effect: there are no crashes); it
may report an error. Over the field it reads. -/
abbrev fdatasync.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ osFile f fd }}
    (App (Val #(functions fdatasync [])) (Val #dbl))
  {{ (err : GoInterface), RET #err; structFieldRef DB go!"file" dbl ↦{dq} f }}

end spec

end bbolt
end EtcdGrove
end Perennial
