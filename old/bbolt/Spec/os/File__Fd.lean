module
public import Proof.os.FileModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `f.Fd()`: the file's descriptor. -/
abbrev os.File.Fd.spec : Prop :=
  ∀ (f : Loc) (fd : w64),
  {{ osFile (GF := GF) f fd }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Fd")) (Val #()))
  {{ RET #fd; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
