/-
`n.childAt(i)` (`node.go`): a branch's child, materialized by `Bucket.node` (panics on a leaf).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the `i`-th child of a branch, now cached with `n` as parent. -/
def node.childAt.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (i : w64),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ ∗ ⌜N.isLeaf = false ∧ uint.nat i < N.inodes.length⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"childAt")) (Val #i))
  {{ (c : Loc), RET #c; ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜∃ CN, C'.nodes c = some CN ∧ CN.parent = n ∧ (∃ x, N.inodes[uint.nat i]? = some x ∧ (CN.pgid = x.pgid ∨ CN.pgid = W64 0))⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
