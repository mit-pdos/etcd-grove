/-
## `(*lessor).Grant(id, ttl)` (`lessor.go:281`)

**Users.** The applier's `LeaseGrant` (`apply/backend.go:84`, 3a), on the apply thread, with the
request's id (chosen by the server: `0` only if the client asked `0` and the generator gave `0`,
never) and TTL. Snippet `lessor.go` (`ReqGrantLookup`).

**Proof sketch.** `id = 0`: `ErrLeaseNotFound` (its global, `init`'s `errIs`). `ttl >
MaxLeaseTTL`: `ErrLeaseTTLTooLarge`. `NewLease` (`NewLease.spec`: a fresh object, its fields owned).
`le.mu.Lock()` (`isLessor`'s lock: the invariant with the ghost current state, which `lessorState`
pins to `ls`); `leaseMap[id]` present: `ErrLeaseExists`, unlock, the state unchanged. Else raise
`l.ttl` to `minLeaseTTL` (`c.minTTL`, `isLessor`'s read-only field); `isPrimary()`: `refresh(0)` or
`forever()` (the object's expiry, under its `expiryMu`: not modelled); `leaseMap[id] = l`;
`persistTo(le.b)` (`Lease.persistTo.spec`: `b.BatchTx()`, `LockInsideApply` with `beApplyTok ls.be`,
4b's `MustUnsafePutLease` moving `beLeases ls.be` to `bkt[id := ttl']`, `Unlock` giving the token
back); the metrics (prometheus: no effect); if primary, the notifier's `RegisterOrUpdate` and
`scheduleCheckpointIfNeeded` (the logger: `isLessor`'s `isLogger`). The ghost step: the object's
`l.mu` invariant made (item set empty, `ls.keys l` cleared: `l` is fresh), its `ID`/`ttl` frozen
(`leaseObj`), the history appended with `ls.grant id l ttl'` (`n + 1`). Unlock.

**Changes** (from `specs-ref`'s `lessor__Grant.lean`). Restated over the lessor's own state
(`lessorState`, `LessorState.grant`) in place of the owner's live list, item map, revokers, the
grant guard (`leaseGranted`), the history `leaseEver`/`leaseLiveFrom`/`leaseReqIs` and the
critical-section contract over mvcc's hook (`csContractA`); the backend write is 4b's
`beLeases`, the hook 4a's `beApplyTok`. **Dropped premises**: the grant guard and the "new id
unless monotone" (`id ∉ U`): the code accepts any id; a re-grant of a revoked id is a new object
(the old one's item set kept, `LessorState.keys`). The new lease's object facts come from the law
`lessorAt_obj` (not repeated here).

**Margin.** The expiry (`refresh`/`forever`), the checkpoint schedule and the bucket record's
`RemainingTTL` (`0`) are not modelled. With the logger: `Debug` is called only when primary with a
checkpointer and a TTL above the checkpoint interval.
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

/-- **Grant lease `id`** (the writer): `ErrLeaseNotFound` for id `0`, `ErrLeaseTTLTooLarge` above
`MaxLeaseTTL`, `ErrLeaseExists` for a live id, nothing changed; else a fresh object `l`, the lease
live with the TTL raised to the minimum, in memory and in the backend's bucket. -/
def lessor.Grant.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (id ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ beApplyTok ls.be }}
    (App (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Grant")) (Val #id)) (Val #ttl))
  {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); beApplyTok ls.be ∗
      ((⌜l = null⌝ ∗ lessorState γ n ls ∗
        (⌜sint.Z id = 0⌝ ∗ errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∨
         ⌜sint.Z id ≠ 0 ∧ maxLeaseTTLGo < sint.Z ttl⌝ ∗
           errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseTTLTooLarge err ∨
         ⌜sint.Z id ≠ 0 ∧ sint.Z ttl ≤ maxLeaseTTLGo ∧ ls.leases (sint.Z id) ≠ none⌝ ∗
           errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseExists err)) ∨
       (⌜err = interface.nil ∧ sint.Z id ≠ 0 ∧ sint.Z ttl ≤ maxLeaseTTLGo ∧
          ls.leases (sint.Z id) = none⌝ ∗
        lessorState γ (n + 1) (ls.grant (sint.Z id) l (grantTTL c (sint.Z ttl))))) }}

end spec
end Lease
end EtcdGrove
end Perennial
