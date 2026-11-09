/-
`copyOnWriteContext.freeNode` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: the package's own methods (internal helper: the spec mirrors the code).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/copyOnWriteContext__freeNode.lean`),
over the realization of the predicates given in `Api.lean`'s and `Internal.lean`'s headers.
Changes: restated over the opaque vocabulary of `Api.lean` and `Internal.lean` (the model
functions renamed `mLookup`, `mInsert`, `mDelete`); otherwise unchanged.
Margin: none known.
-/
module

public import Spec.k8s_io.utils.third_party.forked.golang.btree.Internal

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

/-- `(*copyOnWriteContext[T]).freeNode(n)`: give `n` to the free list if the context
owns it (`ftStored`, or `ftFreelistFull` if the list is full); a node it does not own is
left alone (`ftNotOwned`). It touches only `n`'s own memory, so the caller gives up just
that: an owned node's fields and slices (`nodeShallow`; its children may have gone
elsewhere, as in a merge or a root collapse) or a frozen node. -/
def copyOnWriteContext.freeNode.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗
      ((∃ (is : List (V × K)) (ps : List Loc), nodeShallow (V := V) c (DFrac.own 1) n is ps) ∨
       ∃ t : Tree (V × K), frozen o c f less n t) }}
    (App (Val (c @!! go.GoType.PointerType (copyOnWriteContext.ty T) @!! go!"freeNode"))
      (Val #n))
  {{ (r : w64), RET #r; True }}

end spec

end BTree
end EtcdGrove
end Perennial
