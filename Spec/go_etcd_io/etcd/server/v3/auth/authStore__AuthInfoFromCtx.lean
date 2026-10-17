/-
`authStore.AuthInfoFromCtx` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.auth.ClientIP

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

/-- `as.AuthInfoFromCtx(ctx)`: an auth info (`nil` if auth is disabled or the context has no token) and `nil` or `ErrInvalidAuthToken`. Since PR etcd#22259 its invalid-token warning logs the client IP the context carries (`ClientIPFromContext`, which calls `ctx.Value`): the context is a non-nil one whose `Value(ClientIPContextKey{})` returns (`ctxClientIPOk`). -/

abbrev auth.authStore.AuthInfoFromCtx.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ enabledRd st ∗
      auth.ctxClientIPOk ctx }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromCtx")) (Val #ctx))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); enabledRd st ∗ authInfoRO a ∗ authErrIs err }}

end spec

end EtcdGrove
end Perennial
