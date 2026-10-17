/-
`lease.NewLessor(lg, b, cluster, cfg)` (`lessor.go`): names-only (it recovers the lessor from the
backend and starts the lessor's loop). Lean-first (no Rocq counterpart); the server-construction
unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an axiom at the trust
boundary since unit N4 (2026-10-17, D14d/D14f/D14g), why it is true of the Go code below.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewLessor(lg, b, cl, cfg)`** over the real backend `d` (`b` its `*backend`; D14d): the
lessor at `lp` (`lessorInv`, its configuration and `expiredC`, a reader slot of its lock for the
store, the live set empty, `SetCheckpointer` returns), and the contract of its backend for the
lessor's writes (`lessorBackend`), at the backend's batch lock `Pk` and any frozen post-lock hook
`f`, with one write-back token per write and the reader's open share lent (D14f).

Why it is true of the Go code (`newLessor`, `initAndRecover`, `runLoop`, at the etcd pin):
* `newLessor` allocates the lessor (its maps, `expiredC` a channel of 16, `stopC`, `doneC`), sets
  the configuration's fields (a zero `leaseRevokeRate` defaulted to 1000), then `initAndRecover`:
  `b.BatchTx()`'s `LockOutsideApply` (no hook: the backend open, `bOpen`), `UnsafeCreateLeaseBucket`,
  `MustUnsafeGetAllLeases` (it decodes every record of the `Lease` bucket, a panic on an
  undecodable one: the bucket is fresh, `bkFresh d.γB "lease"`, consumed), `Unlock` (one
  write-back: the token), the heap's `Init`, and `b.ForceCommit()`, which commits first so its
  `Unlock` finds nothing pending and does not write back (the backend's `ForceCommit.spec` charges
  a token: the spec is coarser than the code). Its commit runs the backend's hooks (`isBackend`).
  So the live set is empty (`leaseOwn γl []`).
* `go l.runLoop()`: until the lessor is promoted it only takes its lock, finds no expired lease
  and no due checkpoint; once promoted it sends expired leases on `expiredC` (the server's `run`
  receives them) and calls the checkpointer the server installed (`ckptEffectsOk`).
* The backend's contract (`lessorBackend lp Pk f T R`, used by `Grant` and `Checkpoint` through
  `Lease.persistTo`): `BatchTx()` returns the batch transaction; `LockInsideApply` needs the
  backend open (a share of `bOpen`, in the reader's token `mvcc.bkRTx`, lent) and runs the frozen
  hook `f` under `Pk` (`csContract Pk f`); `UnsafePut` into the `Lease` bucket (created by
  `initAndRecover`; a hook bucket, `bridgeParams`, so the readers' view is unchanged) of an
  8-byte key never fails; `Unlock` writes back at most once (`wbTok`).
* `Lookup(id)` (unit N4, D14h, 2026-10-17: `isApplyLessor`'s `Lookup` clause, a premise of
  `isApplyLessor_of_lessorInv` until then): it read-locks the lessor's `mu` and returns the map's
  lease or `nil`; a lease's `ID` is never written after `NewLease`, its `TTL()` and `Keys()` take the
  lease's own lock and return. The proved `lessor.Lookup.spec` takes a reader slot of `mu` (the
  model's `RWMutex` bounds its readers by the slots); the Go `RWMutex` panics only beyond `2 ^ 30`
  concurrent readers, which no etcd process reaches: the clause takes no slot.
* The reader slots of `mu` (a `sync.RWMutex`, made by `newLessor`): one per reader (D14i,
  2026-10-17: the store's and the apply thread's lease owner each hold one). -/
abbrev lease.NewLessor.spec : Prop :=
  ∀ (lg : Loc) (cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ ⌜lg ≠ null⌝ ∗
      ⌜ckptEffectsOk⌝ ∗ lease.clusterOk cl ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ backend.wbTok d.γB ∗
      bkFresh d.γB go!"lease" }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLessor)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #cl)) (Val #cfg))
  {{ (l : GoInterface), RET #l; backend.bOpen d.γB qo ∗ ∃ (lp : Loc) (γl : GName),
      ⌜l = lease.lessorIface lp⌝ ∗ lease.lessorInv lp γl ∗ lease.lessorCfg lp ∗
      lease.lessorExpiredC lp ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), lease.lessorRdOf γl) ∗
      lease.leaseOwn γl [] ∗ lessorCkptOk l ∗
      □ (∀ f : GoFunc, backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
        lease.lessorBackend lp Pk #f (backend.wbTok d.γB) (mvcc.bkRTx d.γB d.P d.be)) ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.lease.lessor.ty @!! go!"Lookup")) (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ apply.leaseIs l id }}) }}

end spec

end EtcdGrove
end Perennial
