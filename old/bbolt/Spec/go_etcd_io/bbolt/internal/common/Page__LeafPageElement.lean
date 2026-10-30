module
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeIndex

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

/-- `p.LeafPageElement(i)`: the location of element `i` of a leaf page (16 bytes each, after the
16-byte header). -/
abbrev Page.LeafPageElement.spec : Prop :=
  ∀ (l : Loc) (i : w16),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"LeafPageElement")) (Val #i))
  {{ RET #(l +ₗ (16 + 16 * uint.Z i)); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
