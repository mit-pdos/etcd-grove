/-
`BTree.minItems` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/BTree__minItems.lean`),
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

/-- `(*BTree[T]).minItems()`: `degree - 1`. -/
def BTree.minItems.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (t : Loc) (dq : DFrac) (tv : BTree V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ t ↦{dq} tv }}
    (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"minItems")) (Val #()))
  {{ RET #(tv.degree' - W64 1); t ↦{dq} tv }}

end spec

end BTree
end EtcdGrove
end Perennial
