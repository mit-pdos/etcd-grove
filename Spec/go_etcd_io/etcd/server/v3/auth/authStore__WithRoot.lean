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

/-- **`as.WithRoot(ctx)`, auth off**: given `IsAuthEnabled`'s contract at the caller's reader
resource `RD` with the verdict of the mode `off` (`enabledVerdict .off b`, i.e. `b = false`: the
store's own vocabulary, what `IsAuthEnabled.spec` gives of the real store and the server's
`apply.isAuthStore` of its store, `apply.isAuthStore_isAuthEnabled`), it returns `ctx` itself
(`if !as.IsAuthEnabled() { return ctx }`), `RD` back.

Two departures, both deliberate. (1) A restriction of scope: the mode is `off`, so the root-token
branch (`store.go:1180-1212`, a derived context with the root's token) is not proved; the one caller,
the server's revocation, runs with auth off (`srvRevokesLeases`). Extending it is a change of the
spec (the post gains the token branch). (2) It takes the implementation's own call, `IsAuthEnabled`'s
contract at `st`'s method, not an API predicate of the store: an implementation that read
`as.enabled` under `enabledMu` itself would not meet it. The reason: in the mode `off` the server's
store is `NewAuthStore`'s axiom (`authStoreKit_off`), which gives contracts, not `authInv`, so the
caller holds no `authInv` to hand over; with the off-mode store proved, the spec takes
`authInv st R .off ∗ enabledRd st .off` instead.

(Review round 1, S3, 2026-11-06: until then the contract answered `⌜b = false⌝`, which its one
caller converted from `isAuthStore`'s. Review round 2, N1, 2026-11-06: until then over a free mode
`M` with the premise `⌜M = .off⌝`; now at the literal `.off`.) -/
abbrev auth.authStore.WithRoot.spec : Prop :=
  ∀ (st : Loc) (RD : IProp GF) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ RD ∗
      □ ({{ RD }} (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled"))
          (Val #()))
        {{ (b : Bool), RET #b; RD ∗ enabledVerdict .off b }}) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"WithRoot")) (Val #ctx))
  {{ RET #ctx; RD }}

end spec

end EtcdGrove
end Perennial
