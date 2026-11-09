/-
## `(*lessor).Demote()` (`lessor.go:534`)

**Users.** The ready handler's `updateLeadership` (`server.go:769`, 2d), on the raft loop's
goroutine, concurrently with the apply thread and the readers.

**Proof sketch.** `le.mu.Lock()`; each live object's `forever()` (its `expiryMu`); the checkpoint
heap and the notifier replaced by fresh ones (`clearScheduledLeasesCheckpoints`,
`clearLeaseExpiredNotifier`); `demotec` closed if not `nil` (its close right in the invariant,
once: then set to `nil`) and set to `nil`; unlock. Nothing of the model changes.

**Changes** (from `specs-ref`'s `lessor__Demote.lean`): over `isLessor`. **Margin.** The primary
flag and the expiries (time).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Stop being the primary lessor** (any goroutine): no change to the model. -/
def lessor.Demote.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Demote")) (Val #()))
  {{ RET #(); True }}

end spec
end Lease
end EtcdGrove
end Perennial
