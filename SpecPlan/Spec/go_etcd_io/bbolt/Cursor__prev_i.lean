/-
`c.prev()` (`cursor.go`): `Prev` with the raw value and flags (read transactions).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The cursor names its handle
`b` in place of the generations `gs` (the per-path generation counter it replaces was unobservable
state, redundant with ownership).
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

/-- (internal) the previous entry with its flags. -/
def Cursor.prev.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c b p T pos ∗ ⌜T.rw = false⌝ }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"prev")) (Val #()))
  {{ (k v : GoSlice) (fl : w32), RET (PairV #k (PairV #v #fl)); boltTx tx γ q T ∗ ∃ pos', boltCur tx γ c b p T pos' }}

end spec

end Bbolt
end EtcdGrove
end Perennial
