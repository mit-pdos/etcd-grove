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

/-- `f.Name()`: some string (bbolt uses it in messages only). -/
abbrev os.File.Name.spec : Prop :=
  ∀ (f : Loc),
  {{ (True : IProp GF) }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Name")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
