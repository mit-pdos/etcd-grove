/-
`node.get` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/node__get.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` and `Internal.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); otherwise unchanged.
Margin: none known.
-/
module

public import Spec.k8s_io.utils.third_party.forked.golang.btree.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BTree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- `(*node[T]).get(key)`: the item with `key`'s key in the subtree (owned or frozen,
at any fraction). -/
def node.get.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) (t : Tree (V × K))
    (key : V) (k : K) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownNode o c f less dq n t ∗
      o.item key k ∗ allItems o t.elems }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"get")) (Val #key))
  {{ RET (PairV #((mLookup t.elems k).getD (zero_val V)) #((mLookup t.elems k).isSome));
      ownNode o c f less dq n t }}

end spec

end BTree
end EtcdGrove
end Perennial
