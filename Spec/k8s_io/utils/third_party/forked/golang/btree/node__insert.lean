/-
`node.insert` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/node__insert.lean`),
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

/-- `(*node[T]).insert(item, maxItems)` into a subtree that is not full: `item` replaces
the entry with its key, or is added; the replaced item is returned. Splitting full
children on the way down keeps the shape, and the node gains at most one item. -/
def node.insert.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (t : Tree (V × K)) (item : V) (k : K)
    (maxItems : w64) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems → t.items.length < 2 * d - 1 →
  sint.Z maxItems = 2 * d - 1 → 2 ≤ d → d ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n t ∗
      o.item item k ∗ allItems o t.elems }}
    (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"insert")) (Val #item)) (Val #maxItems))
  {{ (old : V) (found : Bool), RET (PairV #old #found);
      ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
      ⌜t'.Shape d h ∧ t'.elems = mInsert o.lt t.elems (item, k) ∧
        t.items.length ≤ t'.items.length ∧ t'.items.length ≤ t.items.length + 1 ∧
        old = (mLookup t.elems k).getD (zero_val V) ∧ found = (mLookup t.elems k).isSome⌝ }}

end spec

end BTree
end EtcdGrove
end Perennial
