/-
`authStore.IsAdminPermitted` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2).
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

/-- `as.IsAdminPermitted(authInfo)`: `nil` or one of the package's errors. -/

abbrev auth.authStore.IsAdminPermitted.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (a : Loc) (info : AuthInfo) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ authRd st R ∗ a ↦{dq} info }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAdminPermitted")) (Val #a))
  {{ (err : GoInterface), RET #err; authRd st R ∗ a ↦{dq} info ∗ authErrIs err }}

end spec

end EtcdGrove
end Perennial
