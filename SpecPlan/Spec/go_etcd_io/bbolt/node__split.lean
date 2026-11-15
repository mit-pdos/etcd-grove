/-
`n.split(pageSize)` (`node.go`): `splitTwo` until the rest is small.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) the pieces, whose inodes concatenate to `N`'s. -/
def node.split.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR) (ps : w64),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"split")) (Val #ps))
  {{ (s : GoSlice), RET #s; ∃ (C' : TxCore) (ls : List Loc), wtxCore tx γ C' ∗ s ↦* ls ∗ ⌜ls.head? = some n ∧ (ls.filterMap (fun l => (C'.nodes l).map NodeR.inodes)).flatten = N.inodes⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
