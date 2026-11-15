/-
`BTree.Clone` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache `newClonedSnapshot` (`cache/snapshot.go:30`): the clone is frozen (`ownBTree_persist`) and read by `Get`s concurrently with writes to the original (snippet `btree/ReqFrozenClone`); mvcc's `treeIndex.Compact` (`index.go:209`: the clone iterated outside the lock while the original is written; snippet `btree/ReqCompactClone`).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/BTree__Clone.lean`),
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

/-- `(*BTree[T]).Clone()`: a second tree with the same entries. Both get fresh
copy-on-write contexts, so neither owns any existing node, which both share frozen;
after it, the two are separate resources (usable from different goroutines). -/
def BTree.Clone.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (s : List (V × K)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t (DFrac.own 1) s }}
    (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"Clone")) (Val #()))
  {{ (t2 : Loc), RET #t2; ownBTree o t (DFrac.own 1) s ∗ ownBTree o t2 (DFrac.own 1) s }}

end spec

end BTree
end EtcdGrove
end Perennial
