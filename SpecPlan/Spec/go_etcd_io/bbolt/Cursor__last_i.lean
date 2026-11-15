/-
`c.last()` (`cursor.go`): the stack moved to the last leaf element.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The handle premise `bktUse`
(the bucket's ownership share in a write transaction) in place of the generation check, given back;
the cursor names its handle `b` in place of `gs` (the per-path generation counter it replaces was
unobservable state, redundant with ownership).
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

/-- (internal) the stack at the last entry. -/
def Cursor.last.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (pos : Option Nat),
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c b p T pos ∗ bktUse tx γ T.rw b p qb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"last")) (Val #()))
  {{ RET #(); bktUse tx γ T.rw b p qb ∗ boltTx tx γ q T ∗ boltCur tx γ c b p T (some ((T.ents p).length - 1)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
