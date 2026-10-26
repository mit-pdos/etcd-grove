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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`le.Recover(b, rd)`** of the lessor `lp` on the real backend at `oldbe` (its user's half of
`le.b`, `lessorBeOn`), no lease live (`leaseOwn γl [] ∅`, the user's half of the live set), onto the
real backend `d` whose lease bucket is empty (absent or empty: the image's, under the workload,
which grants no lease): the lessor on `d`, still no lease, the lease bucket of `d` present and
empty, at two write-back tokens.

Why it is true of the Go code (`lessor.go:600-609`, `initAndRecover` `:808-835` at the etcd pin):
under `le.mu` (the lessor's lock, `lessorInv`: the lock's half of `le.b` with the user's makes the
field whole), `le.b = b`, `le.rd = rd`, fresh `leaseMap` and `itemMap` (the live set was empty,
`leaseOwn`, so the lock's half of it stays `[]` and the maps' empty contents agree), then
`initAndRecover`: `b.BatchTx()`, `LockOutsideApply` (the backend open: the share `qo`),
`UnsafeCreateLeaseBucket` (present or created: its data `∅`), `MustUnsafeGetAllLeases` (no record:
nothing decoded, no panic), `Unlock` (the create's pending operation written back: one token),
the expiry notifier and the checkpoint heap re-initialized empty, `ForceCommit` (one token; its
pre-commit hook runs at the new backend's registered names: `applySnapshot` calls `Recover` after
`ci.SetBackend`). `rd` is stored, not called (no lease to revoke). The lessor's other contracts
(`lessorApplyOk`, for whichever backend the user's half of `le.b` names) stay true. -/
abbrev lease.lessor.Recover.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (oldbe : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (r : GMap GoString backend.BktData) (rd : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γl ∗ lease.lessorBeOn lp oldbe ∗ lease.leaseOwn γl [] ∅ ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ ownToks d.γB.wb 2 ∗
      backend.rbOwn d.γB r ∗ ⌜(r.lookup go!"lease").getD ∅ = ∅⌝ }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Recover")) (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #rd))
  {{ RET #(); lease.lessorBeOn lp d.be ∗ lease.leaseOwn γl [] ∅ ∗ backend.bOpen d.γB qo ∗
      backend.rbOwn d.γB (r.insert go!"lease" ∅) }}

end spec

end EtcdGrove
end Perennial
