/-
`c.Bucket()` (`cursor.go`): the cursor's bucket handle. **Users.** None in etcd.
**Proof sketch.** `c.bucket`. **Changes.** New.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The cursor names its handle
`b` (the result) in place of `gs`; the handle's `bktH` (in a write transaction, the handle premise
stays with the caller's token) (the per-path generation counter it replaces was unobservable state,
redundant with ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `c.Bucket()`: the handle of the cursor's bucket. -/
def Cursor.Bucket.spec : Prop :=
  ∀ [HasExt osFsExt] (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (pos : Option Nat),
  {{ boltCur (GF := GF) tx γ c b p T pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Bucket")) (Val #()))
  {{ RET #b; boltCur tx γ c b p T pos ∗ bktH tx γ b p }}

end spec

end Bbolt
end EtcdGrove
end Perennial
