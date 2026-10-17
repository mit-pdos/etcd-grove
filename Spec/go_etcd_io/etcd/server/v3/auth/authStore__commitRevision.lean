/-
`authStore.commitRevision` (`server/auth/store.go`): the trust boundary (names only).
Lean-first (no Rocq counterpart; PR etcd#21845, `pr-verify/etcd-21845`).
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

/-- `as.commitRevision(tx)`, the batch transaction `tx` held (`H`): returns, `H` kept (it bumps
the atomic `revision` and saves it through `tx`). -/
abbrev auth.authStore.commitRevision.spec : Prop :=
  ∀ (st : Loc) (R W H : IProp GF) (Roles : RolesM → IProp GF) (tx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗
      authBatchTxOk tx W H Roles ∗ H }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"commitRevision")) (Val #tx))
  {{ RET #(); H }}

end spec

end EtcdGrove
end Perennial
