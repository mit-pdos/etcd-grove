/-
`tx.Writable()` (`tx.go`). **Users.** None in etcd. **Proof sketch.** Read `tx.writable`.
**Changes.** New.
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

/-- `tx.Writable()`: whether it is a write transaction. -/
def Tx.Writable.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView),
  {{ boltTx (GF := GF) tx γ q T }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Writable")) (Val #()))
  {{ RET #T.rw; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
