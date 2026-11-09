/-
`BTree.Delete` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache `store.applyEventsLocked` (`cache/store.go:157`): a delete event removes the key's item, and the cache errs if there was none (`ok`), so the returned flag is inspected (snippet `btree/ReqSortedMap`); mvcc's `treeIndex.Compact` (`index.go:218`: `lg.Panic` unless `ok`, deleting from the original while iterating a clone; snippet `btree/ReqCompactClone`).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/BTree__Delete.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); otherwise unchanged.
Margin: none known.
-/
module

public import Spec.k8s_io.utils.third_party.forked.golang.btree.Api

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

/-- `(*BTree[T]).Delete(item)`: remove the entry with `item`'s key. -/
def BTree.Delete.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (s : List (V × K)) (item : V) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t (DFrac.own 1) s ∗ o.item item k }}
    (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"Delete")) (Val #item))
  {{ RET (PairV #((removeOp (.key k) s).2.getD (zero_val V)) #((removeOp (.key k) s).2.isSome));
      ownBTree o t (DFrac.own 1) (removeOp (.key k) s).1 }}

end spec

end BTree
end EtcdGrove
end Perennial
