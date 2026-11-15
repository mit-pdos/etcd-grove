/-
`BTree.AscendGreaterOrEqual` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache `snapshot.Range` (`cache/snapshot.go:41`), a from-key read collecting every item (snippet `btree/ReqSortedMap`); mvcc's `treeIndex.unsafeVisit` (`index.go:98`: stopped early at the end key or a limit; snippets `btree/ReqStopEarly`, `ReqFractionalReaders`).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/BTree__AscendGreaterOrEqual.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); otherwise unchanged.
Margin: none known.
-/
module

public import SpecPlan.Spec.k8s_io.utils.third_party.forked.golang.btree.Api

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

/-- `(*BTree[T]).AscendGreaterOrEqual(...)`: call `iterator` on the entries ascending, from `pivot`, until it returns
false (at any fraction of the tree; the iterator keeps its own state in `I`). -/
def BTree.AscendGreaterOrEqual.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) (pivot : V) (kp : K)
    (iterator : GoFunc) (I : List (V × K) → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t dq s ∗ o.item pivot kp ∗
      iterProtocol o iterator (ascRange o.lt s (some kp) none) I ∗ I [] false }}
    (App (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"AscendGreaterOrEqual")) (Val #pivot)) (Val #iterator))
  {{ RET #(); ownBTree o t dq s ∗ iterDone (ascRange o.lt s (some kp) none) I }}

end spec

end BTree
end EtcdGrove
end Perennial
