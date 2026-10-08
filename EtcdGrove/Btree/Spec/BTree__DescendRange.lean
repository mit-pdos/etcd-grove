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

/-- `(*BTree).DescendRange(...)`: `BTreeG.DescendRange`. -/
abbrev BTree.DescendRange.spec : Prop :=
  ∀ {K : Type} (o : ItemOrder GF GoInterface K) (t : Loc) (dq : DFrac) (s : List (GoInterface × K)) (lessOrEqual : GoInterface) (kle : K) (greaterThan : GoInterface) (kgt : K)
    (iterator : GoFunc) (I : List (GoInterface × K) → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t dq s ∗ o.item lessOrEqual kle ∗ o.item greaterThan kgt ∗
      iterProtocol o iterator (descRange o.lt s (some kle) (some kgt)) I ∗ I [] false }}
    (App (App (App (Val (t @!! go.GoType.PointerType BTree.ty @!! go!"DescendRange")) (Val #lessOrEqual)) (Val #greaterThan)) (Val #iterator))
  {{ RET #(); ownBTree o t dq s ∗ iterDone (descRange o.lt s (some kle) (some kgt)) I }}

end spec

end Btree
end EtcdGrove
end Perennial
