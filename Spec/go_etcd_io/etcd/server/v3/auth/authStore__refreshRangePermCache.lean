/-
`authStore.refreshRangePermCache` (`server/auth/range_perm_cache.go`): the trust boundary
(names only). Lean-first (no Rocq counterpart; PR etcd#21845, `pr-verify/etcd-21845`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvRole

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3 auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.refreshRangePermCache(tx)`, the batch transaction `tx` held (`H`): returns, `H` and the
roles kept (it rebuilds the permission cache, under `rangePermCacheMu`, from the users and roles
it reads through `tx`). -/
abbrev auth.authStore.refreshRangePermCache.spec : Prop :=
  ∀ (st : Loc) (R W H : IProp GF) (Roles : RolesM → IProp GF) (m : RolesM) (tx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗
      authBatchTxOk tx W H Roles ∗ H ∗ Roles m }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
      (Val #tx))
  {{ RET #(); H ∗ Roles m }}

end spec

end EtcdGrove
end Perennial
