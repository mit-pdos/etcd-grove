/-
`c.last()` (`cursor.go`): the stack moved to the last leaf element.
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

/-- (internal) the stack at the last entry. -/
def Cursor.last.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T pos ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"last")) (Val #()))
  {{ RET #(); boltTx tx γ q T ∗ boltCur tx γ c p gs T (some ((T.ents p).length - 1)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
