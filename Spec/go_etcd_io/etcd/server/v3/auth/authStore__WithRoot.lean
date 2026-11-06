/-
`authStore.WithRoot` (`server/auth/store.go`). Lean-first (no Rocq counterpart); revoke-open
(2026-11-06, `notes/revoke-open-plan.md`, "Draft pass 1", I.3): the revocation's inner goroutine
calls `s.authStore.WithRoot(s.ctx)` before `LeaseRevoke`.
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

/-- **`as.WithRoot(ctx)`, auth off** (the only case a caller needs: the server's revocation runs with
auth off, `srvRevokesLeases`): in the mode `off`, given `IsAuthEnabled`'s contract with the mode's
verdict (`enabledVerdict M`, the store's own vocabulary: what `IsAuthEnabled.spec` gives of the real
store and the server's `apply.isAuthStore` of its store, `apply.isAuthStore_isAuthEnabled`) at the
caller's reader resource `RD`, it returns `ctx` itself (`if !as.IsAuthEnabled() { return ctx }`),
`RD` back. (Review round 1, S3, 2026-11-06: until then the contract answered `⌜b = false⌝`, which
its one caller converted from `isAuthStore`'s.) -/
abbrev auth.authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (RD : IProp GF) (M : AuthMode) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ RD ∗ ⌜M = .off⌝ ∗
      □ ({{ RD }} (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled"))
          (Val #()))
        {{ (b : Bool), RET #b; RD ∗ enabledVerdict M b }}) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"WithRoot")) (Val #ctx))
  {{ RET #ctx; RD }}

end spec

end EtcdGrove
end Perennial
