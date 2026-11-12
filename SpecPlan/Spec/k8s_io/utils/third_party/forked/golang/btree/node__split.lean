/-
`node.split` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/node__split.lean`),
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

/-- `(*node[T]).split(i)`: the node keeps the items before `i` (and their children);
item `i` is returned, with a new node holding the items after it (and their children). -/
def node.split.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (is : List (V × K))
    (cs : List (Tree (V × K))) (i : w64) (e : V × K),
  0 ≤ sint.Z i → is[sint.nat i]? = some e → (cs = [] ∨ cs.length = is.length + 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n (.node is cs) }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"split")) (Val #i))
  {{ (n2 : Loc), RET (PairV #e.1 #n2);
      ownedNode o c f less (DFrac.own 1) n
        (.node (is.take (sint.nat i)) (cs.take (sint.nat i + 1))) ∗
      ownedNode o c f less (DFrac.own 1) n2
        (.node (is.drop (sint.nat i + 1)) (cs.drop (sint.nat i + 1))) }}

end spec

end BTree
end EtcdGrove
end Perennial
