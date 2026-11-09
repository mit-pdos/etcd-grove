/-
`c.goToFirstElementOnTheStack()` (`cursor.go`): descends to the first leaf element below the stack's top.
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

/-- (internal) the stack at the first element of the subtree its top points to. -/
def Cursor.goToFirstElementOnTheStack.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"goToFirstElementOnTheStack")) (Val #()))
  {{ RET #(); boltTx tx γ q T ∗ ∃ pos', boltCur tx γ c p gs T pos' }}

end spec

end Bbolt
end EtcdGrove
end Perennial
