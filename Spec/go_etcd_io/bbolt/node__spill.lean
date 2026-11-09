/-
`n.spill()` (`node.go`): children first, then the node split into pages from `tx.allocate`, the parent's keys updated; frees the old page. Users: `Bucket.spill`.
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

/-- (internal) the subtree written to fresh pages, or an error (an allocation's). -/
def node.spill.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜err = GoInterface.nil → ∃ N', C'.nodes n = some N' ∧ N'.spilled = true⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
