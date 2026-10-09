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

/-- `(*node[T]).get(key)`: the item with `key`'s key in the subtree (owned or frozen,
at any fraction). -/
abbrev node.get.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) (t : Tree (V × K))
    (key : V) (k : K) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownNode o c f less dq n t ∗
      o.item key k ∗ allItems o t.elems }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"get")) (Val #key))
  {{ RET (PairV #((lookup t.elems k).getD (zero_val V)) #((lookup t.elems k).isSome));
      ownNode o c f less dq n t }}

end spec

end btree
end EtcdGrove
end Perennial
