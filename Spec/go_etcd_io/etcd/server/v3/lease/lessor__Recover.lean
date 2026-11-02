/-
`(*lease.lessor).Recover(b, rd)` (`lessor.go`): names-only. Lean-first (no Rocq counterpart); D22
receiver epochs, S8c (2026-10-24), for `applySnapshot`; an axiom at the trust boundary
(`Proof/.../lease/lessor__Recover.lean`), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`le.Recover(b, rd)`** of the lessor `lp` on the real backend at `oldbe` (its user's half of
`le.b`, `lessorBeOn`), the user's half of the live set at some `L` with its item map `I` and its
close rights (`leaseOwn γl L I`, `leaseRevokers γl L`), onto the real backend `d` whose lease bucket
is empty (absent or empty: the image's, under the workload, which grants no lease; a part of any
bucket set `S` containing `lease`, `rbPart d.γB S r`, says so; the bucket in the table, tracked,
none of its keys a hook's, `mvcc.leaseParams d.P`, 2026-11-01, E: so the bucket it creates is among
the backend's ghost names, as `rbOwnIn` of the result needs): the lessor on `d`, no lease live
(`leaseOwn γl [] ∅`, `leaseRevokers γl []`), the lease bucket of `d` present and empty, **the part
idle** (`rbOwnIn d.γB S (r.insert "lease" ∅)`), at two write-back tokens. (D22 receiver epochs,
S8d, 2026-10-25, the user's decision: any `L` before, until then `[]`; the apply thread holds the
live set existentially. 2026-11-01, the backend-auth-split stage: until then the whole writer's
half `rbOwn`, in and out.)

Why it is true of the Go code (`lessor.go:600-609`, `initAndRecover` `:808-835` at the etcd pin):
under `le.mu` (the lessor's lock, `lessorInv`: the lock's half of `le.b` with the user's makes the
field whole), `le.b = b`, `le.rd = rd`, fresh `leaseMap` and `itemMap` (empty: the live set's two
halves, the lock's and the user's, both go to `[]`, which the fresh maps' contents are), then
`initAndRecover`: `b.BatchTx()`, `LockOutsideApply` (the backend open: the share `qo`),
`UnsafeCreateLeaseBucket` (present or created: its data `∅`, the part), `MustUnsafeGetAllLeases`
(through the batch transaction: the part's contents, no record: nothing decoded, no panic),
`Unlock` (the create's pending operation written back: one token; after it the readers see the
writer's contents on every bucket, the Go basis: the part idle), the expiry notifier and the
checkpoint heap re-initialized empty, `ForceCommit` (one token; its pre-commit hook runs at the new
backend's registered names: `applySnapshot` calls `Recover` after `ci.SetBackend`). `rd` is stored,
not called (no lease to revoke). The lessor's other contracts (`lessorApplyOk`, for whichever
backend the user's half of `le.b` names) stay true.
(lease-keys Part B, 2026-10-31) **The readers' model**: under `le.mu`, with the owner's half (in
`leaseOwn`/`leaseClosers`), the lock's quarter (the write lock: fraction 1) and the invariant's
quarter (`lessorRdN`, opened inside the call) of the lessor's history, the fresh maps' snapshot
`(∅, ∅)` is appended to it. The invariant survives: `setsOk`, since the new map has no lease, every
old lease's last live index is unchanged, and Go never writes an old lease's `itemSet` again (the
old leases keep their keys there, frozen: `Recover` does not clear them); `histOk`, since `∅` has no
key and no lease is new. The item-sets map is unchanged; the old leases' `closerAt` (the owner's
half of each set, a reader slot of its lock) are dropped, and a reader in an old lease's `Keys()`
keeps the slot it borrowed. The post's `leaseClosers` is at `C = ∅`, `I = ∅`, the history's last
snapshot, with the owner's half of the item-sets map. (The lease-grant plan's D2, 2026-11-02) The
lessor revocable (`lessorRevocable γl`): the appended `(∅, ∅)` drops the live leases, which a
monotone lessor's history (`histMono`) forbids. -/
abbrev lease.lessor.Recover.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (oldbe : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (S : GoString → Prop) (r : GMap GoString backend.BktData) (rd : GoFunc) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
  S go!"lease" → mvcc.leaseParams d.P →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γl ∗ lease.lessorRevocable γl ∗ lease.lessorBeOn lp oldbe ∗
      lease.leaseOwn γl L I ∗
      lease.leaseRevokers γl L ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ ownToks d.γB.wb 2 ∗
      backend.rbPart d.γB S r ∗ ⌜(r.lookup go!"lease").getD ∅ = ∅⌝ }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Recover")) (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #rd))
  {{ RET #(); lease.lessorBeOn lp d.be ∗ lease.leaseOwn γl [] ∅ ∗ lease.leaseRevokers γl [] ∗
      backend.bOpen d.γB qo ∗ backend.rbOwnIn d.γB S (r.insert go!"lease" ∅) }}

end spec

end EtcdGrove
end Perennial
