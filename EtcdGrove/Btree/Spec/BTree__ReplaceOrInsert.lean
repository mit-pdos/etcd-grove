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

/-- `(*BTree).ReplaceOrInsert(item)`: the replaced item, or `nil`. -/
abbrev BTree.ReplaceOrInsert.spec : Prop :=
  ∀ {K : Type} (o : ItemOrder GF GoInterface K) (t : Loc) (s : List (GoInterface × K)) (item : GoInterface) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t (DFrac.own 1) s ∗ o.item item k }}
    (App (Val (t @!! go.GoType.PointerType BTree.ty @!! go!"ReplaceOrInsert")) (Val #item))
  {{ RET #((lookup s k).getD interface.nil); ownBTree o t (DFrac.own 1) (insert o.lt s (item, k)) }}

end spec

end Btree
end EtcdGrove
end Perennial
