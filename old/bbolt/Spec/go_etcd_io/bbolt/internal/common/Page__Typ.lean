module
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsMetaPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
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

/-- The name of a page type. -/
def pageTypName (f : w16) : Option GoString :=
  if f = W16 1 then some go!"branch" else if f = W16 2 then some go!"leaf"
  else if f = W16 4 then some go!"meta" else if f = W16 16 then some go!"freelist" else none

/-- `p.Typ()`: the name of the page's type (`branch`, `leaf`, `meta`, `freelist`; otherwise
some string, `unknown<..>`). -/
abbrev Page.Typ.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"Typ")) (Val #()))
  {{ (s : GoString), RET #s; l ↦{dq} v ∗ ⌜∀ n, pageTypName v.flags' = some n → s = n⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
