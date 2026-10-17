/-
`WithRootInternal(ctx, store)` (`server/auth/store.go`; new in etcd-io/etcd#22493,
`pr-verify/etcd-22493`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/RootCtx.lean`.
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

/-- `WithRootInternal(ctx, as)`, for the real store `as` (`authIface st`: what the server passes,
`s.authStore`, made by `NewAuthStore`): a context `c'`, not nil, derived from `ctx`, which is
- **the fast path**, only when the store's token provider is the built-in JWT one
  (`jwtProvider st`): `c'` carries the root value of the store `st` itself at a revision `rev`
  (the value `as.Revision()` returned: what `WithRoot` would sign into a JWT), so that
  `st.AuthInfoFromCtx(c')` returns root at `rev` (`rootInfoIf`); no token is made;
- **or the fallback**: `as.WithRoot(ctx)`'s result (`authStore.WithRoot.spec`), which adds no
  root value (`ctxRootKept`: `c'` carries `ctx`'s); this is all a store with another provider
  (simple tokens) gets, and a JWT store with auth disabled.
Which branch a JWT store takes is not stated (`IsAuthEnabled`'s spec returns any boolean: the
flag can change at any time).
The revision is not related to the store's current one: `Revision`'s spec returns any value
(as `WithRoot`'s token, it may be stale by the time it is checked, which `isOpPermitted` rejects
with `ErrAuthOldRevision`). -/
abbrev auth.WithRootInternal.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ enabledRd st }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.WithRootInternal)) (Val #(GoInterface.ok ctx)))
      (Val #(authIface st)))
  {{ (c : GoInterface), RET #c; enabledRd st ∗
      ∃ c' : GoInterfaceOk, ⌜c = GoInterface.ok c'⌝ ∗ ctxDerived ctx c' ∗
      ((jwtProvider st ∗ ∃ rev : w64,
          ctxRootIs c' (some (internalRootContextValue.mk st rev))) ∨
        ctxRootKept ctx c') }}

end spec

end EtcdGrove
end Perennial
