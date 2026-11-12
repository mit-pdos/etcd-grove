/-
`c.next()` (`cursor.go`): `Next` with the raw value and flags.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes** (integration I7): also from the state `seek` leaves (`curSt`'s `curPath`, at a leaf's
end: `Cursor.Seek` calls `next` there).
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

/-- (internal) the next entry with its flags. -/
def Cursor.next.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (st : Option Nat ⊕ GoString),
  {{ boltTx (GF := GF) tx γ q T ∗ curSt tx γ c p gs T st }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"next")) (Val #()))
  {{ (k v : GoSlice) (fl : w32), RET (PairV #k (PairV #v #fl)); boltTx tx γ q T ∗ ∃ pos', boltCur tx γ c p gs T pos' }}

end spec

end Bbolt
end EtcdGrove
end Perennial
