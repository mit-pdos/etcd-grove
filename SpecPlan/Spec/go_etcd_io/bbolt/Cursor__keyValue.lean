/-
`c.keyValue()` (`cursor.go`): the stack's current element.
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

/-- (internal) the entry at the position (nil past the end), with its flags. -/
def Cursor.keyValue.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (i : Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T (some i) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ (k v : GoSlice) (fl : w32), RET (PairV #k (PairV #v #fl)); boltTx tx γ q T ∗ boltCur tx γ c p gs T (some i) ∗ ((⌜(T.ents p)[i]? = none ∧ k = slice.nil⌝) ∨ (∃ e, ⌜(T.ents p)[i]? = some e⌝ ∗ txBytes tx γ k e.1)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
