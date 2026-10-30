module
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsMetaPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage

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

/-- The flags of a valid page: exactly one page type. -/
def validPageFlags (f : w16) : Prop := f = W16 1 ∨ f = W16 2 ∨ f = W16 4 ∨ f = W16 16

instance (f : w16) : Decidable (validPageFlags f) := by unfold validPageFlags; infer_instance

/-- `p.IsValidPage()`: the page's flags are one page type. -/
abbrev Page.IsValidPage.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"IsValidPage")) (Val #()))
  {{ RET #(decide (validPageFlags v.flags')); l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
