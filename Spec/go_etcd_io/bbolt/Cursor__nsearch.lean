/-
`c.nsearch(key)` (`cursor.go`): the leaf level of `search`.
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

/-- (internal) the stack's leaf index at the first element not below `key`. -/
def Cursor.nsearch.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (k0 : GoString) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ curPath tx γ c p gs T k0 ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ RET #(); boltTx tx γ q T ∗ key ↦*{dk} kb ∗ curPath tx γ c p gs T kb }}

end spec

end Bbolt
end EtcdGrove
end Perennial
