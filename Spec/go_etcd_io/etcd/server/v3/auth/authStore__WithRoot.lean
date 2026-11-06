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
auth off, `srvRevokesLeases`): given `IsAuthEnabled`'s contract answering `false` at the caller's
reader resource `RD` (what the server's `apply.isAuthStore` gives in the mode `off`), it returns
`ctx` itself (`if !as.IsAuthEnabled() { return ctx }`), `RD` back. -/
abbrev auth.authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (RD : IProp GF) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ RD ∗
      □ ({{ RD }} (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled"))
          (Val #()))
        {{ (b : Bool), RET #b; RD ∗ ⌜b = false⌝ }}) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"WithRoot")) (Val #ctx))
  {{ RET #ctx; RD }}

end spec

end EtcdGrove
end Perennial
