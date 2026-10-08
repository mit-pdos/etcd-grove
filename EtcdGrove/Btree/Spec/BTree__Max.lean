import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.Init
import EtcdGrove.Btree.Item

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

/-- `(*BTree).Max()`: the largest item, or `nil`. -/
abbrev BTree.Max.spec : Prop :=
  ∀ {K : Type} (o : ItemOrder GF GoInterface K) (t : Loc) (dq : DFrac) (s : List (GoInterface × K)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t dq s }}
    (App (Val (t @!! go.GoType.PointerType BTree.ty @!! go!"Max")) (Val #()))
  {{ RET #((s.getLast?.map Prod.fst).getD interface.nil); ownBTree o t dq s }}

end spec

end Btree
end EtcdGrove
end Perennial
