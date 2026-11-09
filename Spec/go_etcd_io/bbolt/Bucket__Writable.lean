/-
`b.Writable()` (`bucket.go`). **Users.** bbolt itself. **Proof sketch.** `b.tx.writable`.
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

/-- `b.Writable()`: whether its transaction is a write transaction. -/
def Bucket.Writable.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (gs : List Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Writable")) (Val #()))
  {{ RET #T.rw; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
