module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Model
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- `(*BTree[T]).DescendLessOrEqual(...)`: call `iterator` on the entries descending, from `pivot`, until it returns
false (at any fraction of the tree; the iterator keeps its own state in `I`). -/
abbrev BTree.DescendLessOrEqual.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) (pivot : V) (kp : K)
    (iterator : GoFunc) (I : List (V × K) → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t dq s ∗ o.item pivot kp ∗
      iterProtocol o iterator (descRange o.lt s (some kp) none) I ∗ I [] false }}
    (App (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"DescendLessOrEqual")) (Val #pivot)) (Val #iterator))
  {{ RET #(); ownBTree o t dq s ∗ iterDone (descRange o.lt s (some kp) none) I }}

end spec

end btree
end EtcdGrove
end Perennial
