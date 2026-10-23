/-
`authStore.lockedReadTx` (`server/auth/store.go`; the fork's d52eec43e, D22k (A):
`issues/etcd-auth-snapshot-closed-backend-panic.md`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.lockedReadTx()` (read-locks `beMu` around `as.be.ReadTx()` and the transaction's
`RLock()`): a read transaction of the backend current under `beMu`, locked (`authReadTxLocked`:
the read resource `R` turned into its held token); `beMu`'s reader slot comes back. -/

abbrev auth.authStore.lockedReadTx.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      beRd st R M ∗ R }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"lockedReadTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; beRd st R M ∗ authReadTxLocked tx R M }}

end spec

end EtcdGrove
end Perennial
