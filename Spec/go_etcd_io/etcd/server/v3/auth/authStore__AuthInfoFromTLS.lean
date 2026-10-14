/-
`authStore.AuthInfoFromTLS` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.AuthInfoFromTLS(ctx)`: an auth info (`nil`, or a fresh one of the first verified chain's common name and the store's revision). The trust boundary (names only): the peer's `credentials.TLSInfo` and its x509 chains are axiomatized types. Go's type assertion `peer.AuthInfo.(credentials.TLSInfo)` panics for a peer whose `AuthInfo` is not a `TLSInfo`; etcd's gRPC servers have TLS credentials or none (`issues/etcd-auth-tls-info-assert.md`): not stated. -/

abbrev auth.authStore.AuthInfoFromTLS.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromTLS")) (Val #ctx))
  {{ (a : Loc), RET #a; authInfoRO a }}

end spec

end EtcdGrove
end Perennial
