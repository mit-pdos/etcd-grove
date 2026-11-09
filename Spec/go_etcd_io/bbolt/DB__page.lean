/-
`db.page(id)` (`db.go`): the mapped page at `id`.
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

/-- (internal) the page `id` of a transaction's snapshot. -/
def DB.page.spec : Prop :=
  ∀ [HasExt osFsExt] (db tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (id : w64) (p : Loc) (bs : List w8),
  {{ boltTx (GF := GF) tx γ q T ∗ txDB tx db ∗ txPage tx γ id p bs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"page")) (Val #id))
  {{ RET #p; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
