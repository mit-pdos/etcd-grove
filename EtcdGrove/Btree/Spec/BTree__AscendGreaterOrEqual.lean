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

/-- `(*BTree).AscendGreaterOrEqual(...)`: `BTreeG.AscendGreaterOrEqual`. -/
abbrev BTree.AscendGreaterOrEqual.spec : Prop :=
  ∀ {K : Type} (o : ItemOrder GF GoInterface K) (t : Loc) (dq : DFrac) (s : List (GoInterface × K)) (pivot : GoInterface) (kp : K)
    (iterator : GoFunc) (I : List (GoInterface × K) → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t dq s ∗ o.item pivot kp ∗
      iterProtocol o iterator (ascRange o.lt s (some kp) none) I ∗ I [] false }}
    (App (App (Val (t @!! go.GoType.PointerType BTree.ty @!! go!"AscendGreaterOrEqual")) (Val #pivot)) (Val #iterator))
  {{ RET #(); ownBTree o t dq s ∗ iterDone (ascRange o.lt s (some kp) none) I }}

end spec

end Btree
end EtcdGrove
end Perennial
