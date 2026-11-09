/-
# etcd's backend as the lessor sees it (batch 4a, integration Y)

The lessor (3c) states its API over the `backend.Backend` value it is given, with its own opaque
names (`Lease.beOk`, `Lease.beHook`, `Lease.beHookRun`, `Lease.beLeases`, `Lease.beTxHeld`); the laws
here introduce each from 4a's resources (integration I5's request of 4a: "laws that introduce `beOk`,
`beHook` and `beLeases` for the lessor"), so the server (2d/2e), which opens the backend and makes the
lessor, can give them. Only the server's proofs import this module.

## Intended realizations (the lessor's names over 4a's)

* `Lease.beOk be := ∃ γ b p Pk, ⌜be = beIface b⌝ ∗ isBackend γ b p Pk ∗ beOpen γ leaseShare`: a
  **fixed** share (`leaseShare`), so that the server gets the same share back for the backend's
  `Close` (`leaseBeOk_elim`; the lessor's `Recover` hands back the old backend's).
* `Lease.beHook be Pk f := ∃ γ b p, ⌜be = beIface b⌝ ∗ isBackend γ b p Pk ∗ beHook γ DFrac.discard f`.
* `Lease.beHookRun be Pk f Pre Q := ∃ γ b p, ⌜be = beIface b⌝ ∗ isBackend γ b p Pk ∗ ∀ q, hookRun γ q
  Pk f Pre Q`: the server's hook, proved once over 4a's contract at every share (its
  `UnsafeConsistentIndex` reads through the lent session, `beSess_rd`), is the lessor's; the same
  proof gives mvcc's by `keyBackend_intro`'s conversion.
* `Lease.beLeases be B := ∃ γ b p Pk C, ⌜be = beIface b⌝ ∗ isBackend γ b p Pk ∗ beCur γ leaseFp C ∗
  beNoVis γ leaseFp ∗ ⌜leaseImg C B⌝`: the lease bucket's batch image (the lessor writes and reads it
  only through the batch transaction, 4b's `Schema.txWr`/`txRd` at `SchemaTx.lean`'s `btView`), its
  cells **untracked** (`beNoVis`: no read transaction reads `lease`), so the lessor may write it in a
  session that publishes other cells (mvcc's, `beTxHeld`).
* `Lease.beTxHeld be := ∃ γ B, ⌜be = GoInterface.ok (Mvcc.storageVal B)⌝ ∗ mvccOn γ B ∗ Mvcc.kbHeld B`:
  mvcc's lent lock, turned by `mvccOn_held` into mvcc's session (`beSess γ q' (mvccFpM m) S`, `m`
  whether `meta` is frozen: verify-round, A10-completeness F2), in which `writable γ (mvccFpM m)
  leaseFp` holds by `beNoVis`, given back `Sess.sameOn (mvccFpM m)` (the lessor's delete touches only
  `lease`, disjoint from `mvccFpM m` for either `m`): 3c's `Revoke` under mvcc's write transaction
  (`examples/specreq/backend/parts.go`'s `ReqLentWrite`).

## Laws

`leaseBeOk_intro`, `leaseBeOk_elim`, `leaseBeHook_intro`, `leaseHookRun_intro`,
`leaseBeLeases_intro`, `leaseBeLeases_elim`, `leaseTxHeld_intro`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.MvccStorage
public import Spec.go_etcd_io.etcd.server.v3.lease.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

/-- **The lessor's share of a backend's open token** (named: a fixed share, so that the server gets
it back whole). -/
def leaseShare : Qp := (1 : Qp).half

section model
variable [GooseExts] [GoGlobalContext]

/-- The `lease` bucket's name (`schema.Lease`). -/
def leaseBkt : GoString := Schema.Bkt.name .lease

/-- **The lessor's part of the image**: the `lease` bucket. -/
def leaseFp : Fp := Fp.bucket leaseBkt

/-- **The lease bucket of `C` holds the leases `B`** (id to stored TTL): 4b's encoding
(`Schema.leaseBktIs`: each record a `leasepb.Lease` under its id's eight bytes), the remaining TTL
dropped; each id an `int64`. -/
def leaseImg (C : Image) (B : Int → Option Int) : Prop :=
  ∃ L, Schema.leaseBktIs (C.ents leaseBkt) L ∧
    (∀ i, B i = (L (W64 i)).map (fun r => sint.Z r.2.1)) ∧
    ∀ i, B i ≠ none → -2 ^ 63 ≤ i ∧ i < 2 ^ 63

end model

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The lessor's open share** of the backend `b`. -/
def leaseBeOk_intro.spec : Prop := ∀ γ b p (Pk : IProp GF),
  isBackend γ b p Pk ∗ beOpen γ leaseShare ⊢ Lease.beOk (beIface b)

/-- **The lessor's open share back** (the server's shutdown or snapshot install closes the backend:
`Lease.lessorState_beOk`, `lessor.Recover`'s old backend). -/
def leaseBeOk_elim.spec : Prop := ∀ γ b p (Pk : IProp GF),
  isBackend γ b p Pk ∗ Lease.beOk (beIface b) ⊢ beOpen γ leaseShare

/-- **The backend's hook, for the lessor.** -/
def leaseBeHook_intro.spec : Prop := ∀ γ b p (Pk : IProp GF) f,
  isBackend γ b p Pk ∗ beHook γ DFrac.discard f ⊢ Lease.beHook (beIface b) Pk f

/-- **A hook run proved over the backend's contract at every share is the lessor's.** -/
def leaseHookRun_intro.spec : Prop := ∀ γ b p (Pk : IProp GF) f (Pre Q : IProp GF),
  isBackend γ b p Pk ∗ (∀ q, hookRun γ q Pk f Pre Q) ⊢ Lease.beHookRun (beIface b) Pk f Pre Q

/-- **The lease bucket, for the lessor**: the opener's part of it (its batch image, untracked). -/
def leaseBeLeases_intro.spec : Prop := ∀ γ b p (Pk : IProp GF) (C : Image) (B : Int → Option Int),
  isBackend γ b p Pk ∗ beCur γ leaseFp C ∗ beNoVis γ leaseFp ∗ ⌜leaseImg C B⌝ ⊢
    Lease.beLeases (beIface b) B

/-- **The lease bucket back** (for the backend's close, and the server's crash argument: the image a
commit leaves holds the leases the lessor last wrote). -/
def leaseBeLeases_elim.spec : Prop := ∀ γ b p (Pk : IProp GF) (B : Int → Option Int),
  isBackend γ b p Pk ∗ Lease.beLeases (beIface b) B ⊢
    ∃ C : Image, beCur γ leaseFp C ∗ beNoVis γ leaseFp ∗ ⌜leaseImg C B⌝

/-- **mvcc's lent lock is the lessor's `beTxHeld`** (`Mvcc.mvccDeleter_rdOk`'s premise). -/
def leaseTxHeld_intro.spec : Prop := ∀ γ (B : Mvcc.MvccStorage),
  mvccOn (GF := GF) γ B ⊢
    □ (Mvcc.kbHeld B ∗-∗ Lease.beTxHeld (GoInterface.ok (Mvcc.storageVal B)))

end laws

end Backend
end EtcdGrove
end Perennial
