/-
`n.nextSibling()` (`node.go`): the parent's next child, or nil.
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

/-- (internal) the next sibling (materialized) or nil. -/
def node.nextSibling.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"nextSibling")) (Val #()))
  {{ (c : Loc), RET #c; ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜c = Loc.null ∨ ∃ CN, C'.nodes c = some CN ∧ CN.parent = N.parent⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
