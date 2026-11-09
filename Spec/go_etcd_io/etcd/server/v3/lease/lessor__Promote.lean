/-
## `(*lessor).Promote(extend)` (`lessor.go:480`): names only (an assumed spec)

**Users.** 2d's `applyEntryNormal` (`server.go:1990`): on the empty entry of a new term, if the
member is the leader, `Promote(s.Cfg.ElectionTimeout())`, on the apply thread.

**Why it is true.** Under `le.mu`: a fresh `demotec`; every live lease's expiry refreshed by
`extend` plus its remaining TTL (wrapping arithmetic, `time.Time.Add`: no panic), registered in the
notifier, `scheduleCheckpointIfNeeded` (the logger's `Debug`: `isLessor`'s `isLogger`, the zero
logger panicking is excluded there, `specs-ref`'s axiom sweep B3-2); with at least
`leaseRevokeRate` (positive: `newLessor` defaults it) leases, the expiries spread by a float
computation and `sort.Sort` by remaining time (`leases[0]` exists). Nothing of the model changes
(the primary flag and the expiries are time). Untranslated (floats, float-to-integer conversions),
so assumed.

**Changes** (from `specs-ref`'s `lessor__Promote.lean`, `lessorInv ∗ lessorCfg`): over `isLessor`,
which carries the logger fact the sweep found missing. **Margin.** The expiries.
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

/-- **Become the primary lessor** (any goroutine): no change to the model. -/
def lessor.Promote.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (extend : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Promote")) (Val #extend))
  {{ RET #(); True }}

end spec
end Lease
end EtcdGrove
end Perennial
