/-
`NewFreeList` (`k8s.io/utils/third_party/forked/golang/btree/btree.go`).
Users: etcd's cache where it calls it (`cache/store.go`, `cache/snapshot.go`), else no caller outside the package (kept: verified before).
Proof sketch: as the old proof (`specs-ref/Proof/k8s_io/utils/third_party/forked/golang/btree/NewFreeList.lean`),
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

/-- `NewFreeList[T](size)`: an empty free list holding up to `size` nodes (`make` needs
`0 ≤ size`). -/
def NewFreeList.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (size : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜0 ≤ sint.Z size⌝ }}
    (App (Val #(functions NewFreeList [T])) (Val #size))
  {{ (f : Loc), RET #f; isFreeList (V := V) f }}

end spec

end BTree
end EtcdGrove
end Perennial
