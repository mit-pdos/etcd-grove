/-
`tx.DB()` (`tx.go`): `tx.db`.

**Users.** `backend.go:604` (`b.readTx.tx.DB()`, then `Stats()` and `Info()`). Snippet:
`ReqBackendRead`. **Proof sketch.** Read `tx.db` (`boltTx`'s share), which `txDB` names.
**Changes.** Unchanged.
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `tx.DB()`: the transaction's `*DB`. -/
def Tx.DB.spec : Prop :=
  ∀ [HasExt osFsExt] (tx db : Loc) (γ : BoltName) (q : Qp) (T : TxView),
  {{ boltTx (GF := GF) tx γ q T ∗ txDB tx db }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"DB")) (Val #()))
  {{ RET #db; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
