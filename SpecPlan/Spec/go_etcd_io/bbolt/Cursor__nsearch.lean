/-
`c.nsearch(key)` (`cursor.go`): the leaf level of `search`.
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

/-- (internal) the stack's leaf index at the first element not below `key`. -/
def Cursor.nsearch.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (k0 : GoString) (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ curPath tx γ c b p T k0 ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"nsearch")) (Val #key))
  {{ RET #(); boltTx tx γ q T ∗ key ↦*{dk} kb ∗ curPath tx γ c b p T kb }}

end spec

end Bbolt
end EtcdGrove
end Perennial
