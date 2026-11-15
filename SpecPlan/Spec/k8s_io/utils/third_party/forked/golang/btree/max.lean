/-
`max` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/max.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` and `Internal.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); otherwise unchanged.
Margin: none known.
-/
module

public import SpecPlan.Spec.k8s_io.utils.third_party.forked.golang.btree.Internal

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

/-- `max[T](n)`: the largest item of the tree rooted at `n` (`nil` for none). -/
def max.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (d : Nat) (dq : DFrac) (n : Loc) (s : List (V × K)),
  2 ≤ d →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ ownRoot o c f less d dq n s }}
    (App (Val #(functions max [T])) (Val #n))
  {{ RET (PairV #((s.getLast?.map Prod.fst).getD (zero_val V)) #(!s.isEmpty));
      ownRoot o c f less d dq n s }}

end spec

end BTree
end EtcdGrove
end Perennial
