/-
`c.search(key, pgid)` (`cursor.go`): descends from a page or node by binary search (`nsearch` at the leaf).
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

/-- (internal) the stack is the search path of `key`. -/
def Cursor.search.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat) (key : GoSlice) (kb : GoString) (dk : DFrac) (id : w64),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T pos ∗ key ↦*{dk} kb ∗ ⌜T.gens p = gs⌝ }}
    (App (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #id))
  {{ RET #(); boltTx tx γ q T ∗ key ↦*{dk} kb ∗ curPath tx γ c p gs T kb }}

end spec

end Bbolt
end EtcdGrove
end Perennial
