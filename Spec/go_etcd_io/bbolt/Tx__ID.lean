/-
`tx.ID()` (`tx.go`): the transaction's txid (`int(tx.meta.Txid())`).

**Users.** None in etcd; bbolt's own logging. **Proof sketch.** Read `tx.meta` (the transaction's).
**Changes.** New. **Margin.** The txid is not in the model (`BoltSt` has none): any value.
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

/-- `tx.ID()`: some integer. -/
def Tx.ID.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView),
  {{ boltTx (GF := GF) tx γ q T }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"ID")) (Val #()))
  {{ (n : w64), RET #n; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
