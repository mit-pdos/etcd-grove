/-
`c.first()` (`cursor.go`): `First` without hiding a bucket's value; its flags say a bucket.
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

/-- (internal) at the first entry, with its raw value and flags. -/
def Cursor.first.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T pos ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"first")) (Val #()))
  {{ (k v : GoSlice) (fl : w32), RET (PairV #k (PairV #v #fl)); boltTx tx γ q T ∗ boltCur tx γ c p gs T (some 0) ∗ (⌜(T.ents p) = [] → k = slice.nil⌝ ∨ ∃ kb, txBytes tx γ k kb) ∗ ⌜∀ e, (T.ents p)[0]? = some e → (e.2 = none ↔ fl ≠ W32 0)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
