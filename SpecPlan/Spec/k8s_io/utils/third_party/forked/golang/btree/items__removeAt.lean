/-
`items.removeAt` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/items__removeAt.lean`),
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

/-- `(*items[T]).removeAt(index)`: the item at `index` is returned and removed, the rest
shifts left (`copy(s[index:], s[index+1:])`); the vacated last slot goes back to the
capacity. -/
def items.removeAt.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T]
    (s : Loc) (sl : GoSlice) (vs : List V) (index : w64) (v : V),
  0 ≤ sint.Z index → vs[sint.nat index]? = some v →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      s ↦ sl ∗ sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) }}
    (App (Val (s @!! go.GoType.PointerType (items.ty T) @!! go!"removeAt")) (Val #index))
  {{ (sl' : GoSlice), RET #v;
      s ↦ sl' ∗ sl' ↦* (vs.take (sint.nat index) ++ vs.drop (sint.nat index + 1)) ∗
      ownSliceCap V sl' (DFrac.own 1) }}

end spec

end BTree
end EtcdGrove
end Perennial
