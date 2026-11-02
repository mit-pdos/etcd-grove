/-
`(*lessor).Renew` (`server/lease/lessor.go`), names only: a trust-boundary contract. Lean-first (no
Rocq counterpart); the lease-renew plan (`notes/lease-renew-plan.md`, 2026-11-01), vocabulary
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`le.Renew(id)`** (names-only, a contract; the lease-renew plan's C1), any goroutine, with the
lessor (`lessorInv`), its reader pool (`lessorRdPool`; a reader slot of its lock until the lease-src
plan, 2026-11-02: `Renew` read-locks `le.mu` first and unlocks it before `l.expired()`,
`lessor.go:396-414`, so the slot is borrowed with the token and given back first) and a thread
token (as `checkLeaseRenew`'s: `l.expired()` read-locks the lease's
`expiryMu`, whose reader slots `isLeaseObj`'s pool lends for one), which it returns: a TTL and
`nil`, or `ErrNotPrimary` (not the primary, or demoted or stopped while waiting for an expired
lease's revocation, or the checkpointer's refusal) or `ErrLeaseNotFound` (no lease of `id`, or it
was revoked while waiting). Nothing is stated of the TTL or of the lease's new expiry, which the
model does not track.

**Why it is faithful.** `Renew` touches only what `le.mu` guards (`lessorMu`): under `le.mu`'s read
lock it reads the lease map, `remainingTTL` and `demotec`; outside it, `l.expired()` reads the
expiry under `l.expiryMu`'s read lock (`Remaining`); it waits on the lease's `revokec`, `demotec`
and `stopC` (receives only); under `le.mu`'s write lock, which it takes through the guard
(`lessorInv`), it reads the lease map again and updates the lease's `expiry` (`refresh`, holding
`l.expiryMu` too, as `leaseMeta` and `leaseExpiry` split it), `remainingTTL`, and the expiry
notifier's heap (`RegisterOrUpdate`, `notifierAt`'s shape kept); then `leaseRenewed.Inc()`, a
metric (not in `leaseInit`: no effect the model sees). It reads `le.cp` without the lock; the
field is written once, by `SetCheckpointer` (under the lock) in `NewServer`
(`etcdserver/server.go:397-410`), before any request goroutine runs. It calls the checkpointer
only if `remainingTTL > 0`; the only checkpointer is `NewServer`'s, which proposes a
`LeaseCheckpoint` request (`raftRequest`, whose result it drops) and returns `nil`, or
`ErrNotPrimary` when `ensureLeadership` fails.

**Its assumption**: that proposal bypasses the proposers' workload (`apply.rqOk` admits no
`LeaseCheckpoint`, D14h); it is covered by the checkpointer's premise `ckptEffectsOk`
(`etcdserver/InvBoot.lean`), which `NewLessor` takes and every closed result carries, whose
docstring names this call too (widened 2026-11-01, approved by the user). It is not exercised today: the server's grant guard is
`False` (`srvGrantGuard`), so every lessor of the closed results has no lease and `Renew`
returns before it reads `cp`. The lease-grant work must revisit this contract. -/
abbrev lease.lessor.Renew.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRdPool γl ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Renew")) (Val #id))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); threadTok ∗
      (⌜err = GoInterface.nil⌝ ∨
      (∃ e : GoInterfaceOk, globalAddr ErrNotPrimary ↦□ GoInterface.ok e ∗
        ⌜err = GoInterface.ok e⌝) ∨
      (∃ e : GoInterfaceOk, globalAddr ErrLeaseNotFound ↦□ GoInterface.ok e ∗
        ⌜err = GoInterface.ok e⌝)) }}

end spec

end EtcdGrove
end Perennial
