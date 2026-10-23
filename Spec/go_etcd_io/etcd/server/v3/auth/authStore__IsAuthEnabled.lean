/-
`authStore.IsAuthEnabled` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.IsAuthEnabled()` (read-locks `enabledMu`): `enabled`. -/

abbrev auth.authStore.IsAuthEnabled.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ enabledRd st }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled")) (Val #()))
  {{ (b : Bool), RET #b; enabledRd st }}

end spec

end EtcdGrove
end Perennial
