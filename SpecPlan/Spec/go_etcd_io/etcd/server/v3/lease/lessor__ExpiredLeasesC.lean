/-
## `(*lessor).ExpiredLeasesC()` (`lessor.go:611`)

**Users.** 2d's `run` (`server.go:835`): the expiry arm of its `select` (`case leases :=
<-expiredLeaseC: s.revokeExpiredLeases(leases)`). Snippet `lessor.go` (`ReqExpiredChannel`).

**Proof sketch.** Returns `le.expiredC`, a read-only field: `isLessor`'s `expiredCh γ c ch`. Its
receive law (`expiredCh_recv`): the run loop (`revokeExpiredLeases` of the lessor, every 500 ms)
sends slices of live objects it found expired, only when primary, and only with the expiry mode on
(with it off, an expiry would contradict the trusted `leasesOutliveRun` taken at `NewLessor`).

**Changes** (from `specs-ref`'s `lessor__ExpiredLeasesC.lean`, the payload `⌜¬ leasesNoExpiry⌝ ∗
∃ id, GA id` of the grant guard): the payload is the objects (`expiredSl`, 2d's provisional
`expiredLeases`), gated by the configuration's expiry mode. **Margin.** Which leases are sent
(time).
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

/-- **The expiry channel** (any goroutine). -/
def lessor.ExpiredLeasesC.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"ExpiredLeasesC")) (Val #()))
  {{ (ch : GoChan), RET #ch; expiredCh γ c ch }}

end spec
end Lease
end EtcdGrove
end Perennial
