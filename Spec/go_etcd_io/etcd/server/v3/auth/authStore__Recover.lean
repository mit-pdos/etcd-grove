/-
`(*auth.authStore).Recover(be)` (`store.go`): names-only. Lean-first (no Rocq counterpart); D22
receiver epochs, S8c (2026-10-24), for `applySnapshot`; an axiom at the trust boundary
(`Proof/.../auth/authStore__Recover.lean`), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

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

/-- **`as.Recover(ab)`** of the auth store `stl` (`NewAuthStore`'s, auth off: mode `.off`) on the
real backend at `oldbe` (its user's half of `as.be`, `authBeOn`), `ab` a schema auth backend over
the real backend `d` (`NewAuthBackend`'s fields, a logger) whose auth buckets are the boot ones (no
`authEnabled` key, no user, no role: the image's, under the workload, `bkRestAt_boot`): the store
on `d`, still disabled. A reader token of `d` (its read transaction's lock) is borrowed.

Why it is true of the Go code (`auth/store.go:399-418` at the etcd pin): `as.beMu.Lock()` (the
lock's half of `as.be` with the user's makes the field whole), `as.be = be`, `Unlock`; then
`be.ReadTx()` and its `RLock` (the backend open, a reader's token: `bkRTx`), `UnsafeReadAuthEnabled`
(no `authEnabled` key: `false`), `UnsafeReadAuthRevision` (some revision, stored by `setRevision`:
the store's revision invariant in mode `.off` asks nothing of it), `refreshRangePermCache` (under
its lock, the users read: none, the cache emptied, nothing decoded), `RUnlock`; under `enabledMu`
`as.enabled = false` (it was: mode `.off`), the token provider not enabled. The store's other
contracts stay true: `authApplyOk stl RD` is for whichever backend the user's half of `as.be`
names (S7c), and `isReqAuth st RD`'s and the permission checks' `RD` names no backend's read
rights in mode `.off` (with auth disabled the checks return before reading the backend,
`isOpPermitted`'s and `IsAdminPermitted`'s `!as.IsAuthEnabled()`; `notes/decisions.md`, "D22
receiver epochs, S8c carried out", W2). -/
abbrev auth.authStore.Recover.spec : Prop :=
  ∀ (stl oldbe abl lg : Loc) (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp)
    (r : GMap GoString backend.BktData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      authBeOn stl oldbe ∗ ⌜lg ≠ null⌝ ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
          #d.be : GoInterface) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ mvcc.bkRTx d.γB d.P d.be ∗
      backend.rbOwn d.γB r ∗
      ⌜(r.lookup go!"auth").getD ∅ = authBoot ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
        (r.lookup go!"authRoles").getD ∅ = ∅⌝ }}
    (App (Val (stl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #(authBkIface abl)))
  {{ RET #(); authBeOn stl d.be ∗ backend.bOpen d.γB qo ∗ mvcc.bkRTx d.γB d.P d.be ∗
      backend.rbOwn d.γB r }}

end spec

end EtcdGrove
end Perennial
