/-
`authStore.AuthInfoFromCtx` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.RootCtx

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

/-- `as.AuthInfoFromCtx(ctx)`, for a context (not nil) that carries the root value `o`
(`ctxRootIs`; every context carries one, `context.ValueInternalRoot.spec`): an auth info (`nil`
if auth is disabled or the context has no token) and `nil` or `ErrInvalidAuthToken`; and, since
etcd-io/etcd#22493 (`pr-verify/etcd-22493`), for a root value of this store, no error and `nil`
or root at the value's revision, whatever token the request carries (`rootInfoIf`). Before the
PR the spec took any context (`nil` too: grpc's `FromIncomingContext`, at the trust boundary, hid
that `ctx.Value` panics on it) and had no `rootInfoIf`; `spec_implies_old` (the proof file)
derives that spec, for a context not nil. -/
abbrev auth.authStore.AuthInfoFromCtx.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterfaceOk) (o : Option internalRootContextValue),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ enabledRd st ∗
      ctxRootIs ctx o }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromCtx")) (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); enabledRd st ∗ authInfoRO a ∗ authErrIs err ∗
      rootInfoIf st o a err }}

end spec

end EtcdGrove
end Perennial
