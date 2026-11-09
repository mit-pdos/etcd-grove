/-
## `(*lessor).Recover(b, rd)` (`lessor.go:600`)

**Users.** 2d's `applySnapshot` (`server.go:1087`): over the backend opened from a received
snapshot's image (`newbe`), with a deleter of the KV store (`s.kv.Write`), before mvcc's `Restore`
(which re-attaches the keys: `Attach`), on the apply thread. Snippet `lessor.go` (`ReqRecover`).

**Proof sketch.** `le.mu.Lock()`; `le.b = b`, `le.rd = rd` (both halves), fresh `leaseMap`,
`itemMap`; `initAndRecover()` (`lessor.initAndRecover.spec`: `b.BatchTx()`, `LockOutsideApply`
(`beOk b`), 4b's `UnsafeCreateLeaseBucket` (the bucket exists: no change to `B`) and
`MustUnsafeGetAllLeases` (its records decode: `beLeases b B`, each id once, in some order), `Unlock`; for each record a fresh
`*Lease` with the TTL raised to the minimum, an empty item set, its own `revokec`; the notifier's
`Init`, `heap.Init` of the checkpoint heap; `b.ForceCommit()`); the history appended with the
loaded state (`n + 1`); the old backend's bucket and open share (`beLeases ls.be ls.bkt`, `beOk
ls.be`, held in the writer's token) go back to the caller (2d's `applySnapshot` closes the old
backend), the new one's into the token; unlock. The old objects' item sets are kept (readers may hold them).

**Changes** (from `specs-ref`'s `lessor__Recover.lean`, the lease-expiry plan's S1 over the
backend's tracked buckets): over the lessor's state and 4b's `beLeases`. **Integration (I5).** The old backend's open share `beOk ls.be` is handed back too (4a: `beOk` is
no longer persistent, `req/..._lease.md`, "from 4a"). **Margin.** The old
objects' `revokec` are never closed (a `Renew` waiting on one waits for `demotec` or `stopC`).
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

/-- **Reload from backend `b`** (the writer): the leases of `b`'s lease bucket `B` (fresh objects,
TTLs raised to the minimum, no key attached), `b` and `rd` the lessor's backend and deleter; the old
backend's bucket and open share handed back. -/
def lessor.Recover.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (b : GoInterface) (rd : GoFunc)
    (B : Int → Option Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ beOk b ∗ beLeases b B }}
    (App (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Recover")) (Val #b)) (Val #rd))
  {{ RET #(); ∃ objs : Int → Loc, beOk ls.be ∗ beLeases ls.be ls.bkt ∗
      lessorState γ (n + 1) (LessorState.loaded c b rd B objs ls.keys) }}

end spec
end Lease
end EtcdGrove
end Perennial
