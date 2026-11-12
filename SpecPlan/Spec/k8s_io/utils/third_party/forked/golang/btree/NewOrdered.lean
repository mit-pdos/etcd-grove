/-
`NewOrdered` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: no caller in etcd; an ordered tree (snippet `btree/ReqOrdered`).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/NewOrdered.lean`),
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

/-- `NewOrdered[T](degree)`: an empty tree of an ordered type, by `<`. -/
def NewOrdered.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (ltb : V → V → Bool)
    (hord : StrictOrder (fun a b => ltb a b = true)),
  ∀ (degree : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜(∀ a b : V, ⟦GoOp GoLt T, (#a, #b)⟧ ⤳[under] #(ltb a b)) ∧ 1 < sint.Z degree ∧
        sint.Z degree ≤ 2 ^ 62⌝ }}
    (App (Val #(functions NewOrdered [T])) (Val #degree))
  {{ (t : Loc), RET #t; ownBTree (orderedOrder (GF := GF) _ hord) t (DFrac.own 1) [] }}

end spec

end BTree
end EtcdGrove
end Perennial
