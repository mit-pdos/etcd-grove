module
public import Spec.go_etcd_io.bbolt.internal.common.Page__Typ
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `p.String()`: some string. -/
abbrev Page.String.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
