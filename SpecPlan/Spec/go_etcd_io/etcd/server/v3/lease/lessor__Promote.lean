/-
## `(*lessor).Promote(extend)` (`lessor.go:480`): names only (an assumed spec)

**Users.** 2d's `applyEntryNormal` (`server.go:1990`): on the empty entry of a new term, if the
member is the leader, `Promote(s.Cfg.ElectionTimeout())`, on the apply thread.

**Why it is true.** Under `le.mu`: a fresh `demotec`; every live lease's expiry refreshed by
`extend` plus its remaining TTL (wrapping arithmetic, `time.Time.Add`: no panic), registered in the
notifier, `scheduleCheckpointIfNeeded` (the logger's `Debug`: `isLessor`'s `isLogger`, the zero
logger panicking is excluded there, `specs-ref`'s axiom sweep B3-2); with at least
`leaseRevokeRate` (non-negative: `NewLessor`'s premise; `0` defaulted to 1000) leases, the expiries spread by a float
computation and `sort.Sort` by remaining time (`leases[0]` exists). Nothing of the model changes
(the primary flag and the expiries are time). **The checkpointer's gate** (round 1): from now on
the lessor is primary and may call its checkpointer (`Renew`, the run loop): `Promote` deposits
`□ R` of `ckptGate le R` in the invariant beside `demotec`. Untranslated (floats, float-to-integer conversions),
so assumed.

**Changes** (from `specs-ref`'s `lessor__Promote.lean`, `lessorInv ∗ lessorCfg`): over `isLessor`,
which carries the logger fact the sweep found missing. **Margin.** The expiries.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **Become the primary lessor** (any goroutine, the checkpointer's gate `R` holding): no change
to the model. -/
def lessor.Promote.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (extend : time.Duration) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      ckptGate le R ∗ □ R }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Promote")) (Val #extend))
  {{ RET #(); True }}

end spec
end Lease
end EtcdGrove
end Perennial
