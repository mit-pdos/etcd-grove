/-
`n.pageElementSize()` (`node.go`): 16 for both kinds.
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

/-- (internal) `16`. -/
def node.pageElementSize.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"pageElementSize")) (Val #()))
  {{ (z : w64), RET #z; wtxCore tx γ C ∗ ⌜uint.nat z = elemSize⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
