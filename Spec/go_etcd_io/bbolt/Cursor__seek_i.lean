/-
`c.seek(key)` (`cursor.go`): `search`, then `next` past a leaf's end.
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

/-- (internal) at the first entry not below `key`, with its raw value and flags. -/
def Cursor.seek.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (p : BPath) (gs : List Nat) (pos : Option Nat) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c p gs T pos ∗ key ↦*{dk} kb ∗ ⌜T.gens p = gs⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (k v : GoSlice) (fl : w32), RET (PairV #k (PairV #v #fl)); boltTx tx γ q T ∗ key ↦*{dk} kb ∗ boltCur tx γ c p gs T (some (seekIdx (T.ents p) kb)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
