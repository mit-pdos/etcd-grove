/-
`authStore.WithRoot` (`server/auth/store.go`): the trust boundary (names only: it signs a root
token with the token provider's `assign`, which the request side does not translate).
Lean-first (no Rocq counterpart; etcd-io/etcd#22493, `pr-verify/etcd-22493`: the fallback of
`WithRootInternal`).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.WithRoot(ctx)`: a context derived from `ctx` (`ctx` itself when auth is disabled or the
token cannot be made, else grpc's `NewIncomingContext(ctx, md)` with a root token in `md`), not
nil, which carries `ctx`'s root value (`ctxRootKept`: grpc's `mdIncomingKey{}` is not
`internalRootContextKey{}`). It reads `enabled` under `enabledMu` (`IsAuthEnabled`: a reader slot). What its token
authenticates is not stated (no caller's proof needs it). -/
abbrev auth.authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ enabledRd st }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"WithRoot")) (Val #(GoInterface.ok ctx)))
  {{ (c : GoInterface), RET #c; enabledRd st ∗
      ∃ c' : GoInterfaceOk, ⌜c = GoInterface.ok c'⌝ ∗ ctxDerived ctx c' ∗ ctxRootKept ctx c' }}

end spec

end EtcdGrove
end Perennial
