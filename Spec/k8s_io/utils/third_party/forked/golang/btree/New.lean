/-
`New` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache `newStore` (`cache/store.go:42`) and `store.Restore` (`:109`), a tree of `*kvItem` by `kvItemLess` at the configured degree (snippet `btree/ReqSortedMap`).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/New.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); the pure premises moved into the precondition; otherwise unchanged.
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

/-- `New[T](degree, less)`: an empty tree (with a free list of its own). -/
def New.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (degree : w64) (less : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜1 < sint.Z degree ∧ sint.Z degree ≤ 2 ^ 62⌝ ∗ isLess o less }}
    (App (App (Val #(functions New [T])) (Val #degree)) (Val #less))
  {{ (t : Loc), RET #t; ownBTree o t (DFrac.own 1) [] }}

end spec

end BTree
end EtcdGrove
end Perennial
