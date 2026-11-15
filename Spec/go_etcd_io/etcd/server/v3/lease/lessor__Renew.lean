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
`lessor.go:396-414`, so the slot is borrowed with the token and given back first) and the level-0
token of the leveled pools (`levelTok lessorLvl`; as `checkLeaseRenew`'s: `l.expired()` read-locks
the lease's `expiryMu`, whose reader slots `isLeaseObj`'s level-0 pool lends for one, after the
lessor's slot is given back), which it returns: a TTL and
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
metric (not in `leaseInit`: no effect the model sees). It reads `le.cp` under `le.mu`'s read lock (`lessor.go:412`), which `lessorMu` holds at `nil`
(`lessorExtra`; stage B3, 2026-11-12): `newLessor` does not set it (`lessor.go:225-242`), its only
writer is `SetCheckpointer` (`lessor.go:274-279`), which `NewServer` calls only with the
`LeaseCheckpoint` feature on (`etcdserver/server.go:393-405`), and the model has no contract for it
(`NewServer.spec` takes the feature off, `featureIs … go!"LeaseCheckpoint" false`, which
`features.NewDefaultServerFeatureGate` gives: its default, `server/features/etcd_features.go:104`).
So `clearRemainingTTL` is `false` and `Renew` never calls a checkpointer (`lessor.go:436-440`): on
its path the lessor's reader slot and the level-0 token are all the locks it takes need.

**Out of scope**: a lessor with a checkpointer installed. Its call (`NewServer`'s closure:
`ensureLeadership`, then `raftRequest` of a `LeaseCheckpoint`, `server.go:395-404`) takes the
server's reader slots, among them `srvLeadTimeReader s ∗ E.RD` of the level-2 pool, and proposes a
request the proposers' workload does not admit (`apply.rqOk`, D14h); a change that turns the
feature on must give the checkpointer a contract and revisit this one. -/
abbrev lease.lessor.Renew.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRdPool γl ∗ levelTok lessorLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Renew")) (Val #id))
  {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err); levelTok lessorLvl ∗
      (⌜err = GoInterface.nil⌝ ∨
      (∃ e : GoInterfaceOk, globalAddr ErrNotPrimary ↦□ GoInterface.ok e ∗
        ⌜err = GoInterface.ok e⌝) ∨
      (∃ e : GoInterfaceOk, globalAddr ErrLeaseNotFound ↦□ GoInterface.ok e ∗
        ⌜err = GoInterface.ok e⌝)) }}

end spec

end EtcdGrove
end Perennial
