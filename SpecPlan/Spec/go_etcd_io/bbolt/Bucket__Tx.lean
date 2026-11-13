/-
`b.Tx()` (`bucket.go`). **Users.** None in etcd. **Proof sketch.** `b.tx`, immutable (a persistent
share in `bktH`). **Changes.** New.
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** `bktH` without the
generations (any handle: `b.tx` is immutable, so a stale handle's `Tx` is fine) (the per-path
generation counter it replaces was unobservable state, redundant with ownership).
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

/-- `b.Tx()`: the handle's transaction. -/
def Bucket.Tx.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (b : Loc) (p : BPath),
  {{ bktH (GF := GF) tx γ b p }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Tx")) (Val #()))
  {{ RET #tx; True }}

end spec

end Bbolt
end EtcdGrove
end Perennial
