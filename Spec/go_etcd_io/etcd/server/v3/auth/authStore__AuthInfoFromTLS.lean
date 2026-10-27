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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.AuthInfoFromTLS(ctx)`: an auth info (`nil`, or a fresh one of the first verified chain's common name and the store's revision). The trust boundary (names only): the peer's `credentials.TLSInfo` and its x509 chains are axiomatized types. For any context: a peer whose `AuthInfo` is not a `TLSInfo` gets `nil` (the fork's checked assertion `tlsInfo, ok := peer.AuthInfo.(credentials.TLSInfo)`, D19l; at upstream's pin the one-result assertion panics, `issues/nonissues/etcd-auth-tls-info-assert.md`). -/

abbrev auth.authStore.AuthInfoFromTLS.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromTLS")) (Val #ctx))
  {{ (a : Loc), RET #a; authInfoRO a }}

end spec

end EtcdGrove
end Perennial
