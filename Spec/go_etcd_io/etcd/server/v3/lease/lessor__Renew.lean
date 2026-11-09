/-
## `(*lessor).Renew(id)` (`lessor.go:396`): names only (an assumed spec)

**Users.** 2c's `EtcdServer.LeaseRenew` on the leader (`v3_server.go:528`: `ErrNotPrimary` makes it
forward to the leader, other errors are returned), and the lease HTTP handler (`leasehttp`, the
leader's side of a forwarded keep-alive; untranslated). Any goroutine. Snippet `lessor.go`
(`ReqRenew`).

**Why it is true** (the code). `le.mu.RLock()`; not primary: `ErrNotPrimary`. `leaseMap[id]` absent
(at the current state `j ≥ i`): `ErrLeaseNotFound`. Else `RUnlock`; `l.expired()` (time): wait on
`l.revokec` (closed by `Revoke` after the lease left the map: `ErrLeaseNotFound`, at that later
state), `demotec` or `stopC` (`ErrNotPrimary`). A checkpointer and a checkpointed remaining TTL: `cp(
context.Background(), &LeaseCheckpointRequest{...})` (`ckptOk`: `nil` or `ErrNotPrimary`, returned
as is; `Context.ctxOk_background`); `le.mu.Lock()`; `leaseMap[id]` absent: `ErrLeaseNotFound`; else
`refresh(0)` and the notifier (time), unlock, `l.ttl` of the live object. Untranslated (time,
channels of the expiry), so assumed.

**Changes** (from `specs-ref`, which had none: the lease-renew plan's contract was the server's):
answered from the lessor's history. **Margin.** Liveness: a renewal tells nothing of the lease's
expiry (time is not modelled; W0's keep-alive step allows any TTL). Whether `ErrNotPrimary` is
answered depends on the primary flag and the clock, not modelled: it may be answered any time.
**Round 1.** A reader token (`lessorReaders γ 1`: the slot of the `RWMutex` it read-locks; the
writer borrows one, `lessorState_reader`), the bounds plan's reader slots.
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

/-- **Renew lease `id`** (any goroutine): its granted TTL, live at a state `j ≥ i`; or
`ErrLeaseNotFound`, not live at a state `j ≥ i`; or `ErrNotPrimary`. -/
def lessor.Renew.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (i : Nat) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorReaders γ 1 ∗ lessorLb γ i }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Renew")) (Val #id))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err);
      lessorReaders γ 1 ∗ (⌜err = interface.nil⌝ ∗ ∃ (j : Nat) (ls : LessorState) (e : LeaseEnt),
        ⌜i ≤ j ∧ ls.leases (sint.Z id) = some e ∧ sint.Z ttl = e.ttl⌝ ∗ lessorAt γ j ls) ∨
      (errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗ ∃ (j : Nat) (ls : LessorState),
        ⌜i ≤ j ∧ ls.leases (sint.Z id) = none⌝ ∗ lessorAt γ j ls) ∨
      errIs go_etcd_io.etcd.server.v3.lease.ErrNotPrimary err }}

end spec
end Lease
end EtcdGrove
end Perennial
