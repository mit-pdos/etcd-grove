/-
`NewWithFreeList` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache where it calls it (`cache/store.go`, `cache/snapshot.go`), else no caller outside the package (kept: verified before).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/NewWithFreeList.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); the pure premises moved into the precondition; otherwise unchanged.
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

/-- `NewWithFreeList[T](degree, less, f)`: an empty tree using the free list `f`.
`degree <= 1` panics; above `2^62`, `maxItems()` overflows. -/
def NewWithFreeList.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (degree : w64) (less : GoFunc) (f : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜1 < sint.Z degree ∧ sint.Z degree ≤ 2 ^ 62⌝ ∗ isLess o less ∗ isFreeList (V := V) f }}
    (App (App (App (Val #(functions NewWithFreeList [T])) (Val #degree)) (Val #less)) (Val #f))
  {{ (t : Loc), RET #t; ownBTree o t (DFrac.own 1) [] }}

end spec

end BTree
end EtcdGrove
end Perennial
