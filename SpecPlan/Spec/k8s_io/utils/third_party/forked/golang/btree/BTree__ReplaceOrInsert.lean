/-
`BTree.ReplaceOrInsert` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache `store.Restore` (`cache/store.go:111`) and `store.applyEventsLocked` (`:161`): a put replaces the key's item (snippet `btree/ReqSortedMap`); mvcc's `treeIndex.Put`, `Insert` (`index.go:62, 265`).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/BTree__ReplaceOrInsert.lean`),
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

/-- `(*BTree[T]).ReplaceOrInsert(item)`: `item` replaces the entry with its key (which is
returned, with `true`), or is added (returning the zero value and `false`). -/
def BTree.ReplaceOrInsert.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (s : List (V × K)) (item : V) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t (DFrac.own 1) s ∗ o.item item k }}
    (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"ReplaceOrInsert")) (Val #item))
  {{ RET (PairV #((mLookup s k).getD (zero_val V)) #((mLookup s k).isSome));
      ownBTree o t (DFrac.own 1) (mInsert o.lt s (item, k)) }}

end spec

end BTree
end EtcdGrove
end Perennial
