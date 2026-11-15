/-
`BTree.Has` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache where it calls it (`cache/store.go`, `cache/snapshot.go`), else no caller outside the package (kept: verified before).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/BTree__Has.lean`),
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

/-- `(*BTree[T]).Has(key)`: whether there is an entry with `key`'s key. -/
def BTree.Has.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) (key : V) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownBTree o t dq s ∗ o.item key k }}
    (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"Has")) (Val #key))
  {{ RET #((mLookup s k).isSome); ownBTree o t dq s }}

end spec

end BTree
end EtcdGrove
end Perennial
