/-
`tx.page(id)` (`tx.go`): the transaction's dirty page, else the mapped one (`FastCheck`).
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

/-- (internal) page `id` of the transaction's snapshot. -/
def Tx.page.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (id : w64) (p : Loc) (bs : List w8),
  {{ boltTx (GF := GF) tx γ q T ∗ txPage tx γ id p bs }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"page")) (Val #id))
  {{ RET #p; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
