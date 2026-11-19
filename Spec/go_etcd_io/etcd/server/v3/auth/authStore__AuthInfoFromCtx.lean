/-
`authStore.AuthInfoFromCtx` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.context.LibKeys
public import Proof.go_etcd_io.etcd.server.v3.auth.WhyDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.AuthInfoFromCtx(ctx)`, read by a reader with the lower bound `n` of the store's published index
(`authPubLbM`): an auth info (`nil` if auth is disabled or the context has no token) and `nil` or
`ErrInvalidAuthToken`; the info is bound to the token `tok` the context carries (`ctxBound`; in `on γa`,
its user is one the token was issued to; the auth plan's S5). The context's metadata is needed only when
auth is on (`□ (⌜M.isOn⌝ → ctxToken ctx tok)`: `store.go` reads it only past `IsAuthEnabled()`; perheap
C1a, the token a parameter, 2026-11-18: until then by the context, through the pure `ctxTokenOf`). On
`(nil, nil)` no principal from the request side (`noPrincipalFrom`: the flag read `true` at a state no
older than `n` and no token, or `false` at such a state; the second is how the flag races reach a guard,
`nonissues/etcd-auth-requireauthinfo-disable-race-user-empty.md`, `nonissues/etcd-admin-check-authenable-race.md`);
on an error `ErrInvalidAuthToken` for a token the context carries (`tokRefusedFrom`: only that; the token
provider's contract says nothing when it refuses, token liveness is the auth-guard Scope's G5); with a
principal the flag read `true` at such a state (`store.go:1073`; auth-guard-completeness G1/G4). One spec
(perheap C1a merged the former `spec` and `specLb`): a caller without a bound takes `n := 0`
(`authPubLbM_zero`). -/
abbrev auth.authStore.AuthInfoFromCtx.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (ctx : GoInterfaceOk)
    (tok : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      enabledRd st M ∗ □ (⌜M.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ tpReady M ∗
      auth.ctxDoneRecv ctx ∗ authPubLbM M n }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); enabledRd st M ∗ authInfoRO a ∗
      authErrIs err ∗ ctxBound M tok a ∗
      (∀ _ : a = null ∧ err = GoInterface.nil, auth.noPrincipalFrom M n tok) ∗
      (∀ _ : err ≠ GoInterface.nil, authErrOf .invalidAuthToken err ∗ enabledVerdictFrom M n true ∗
        auth.tokRefusedFrom M n tok) ∗
      (∀ _ : a ≠ null, enabledVerdictFrom M n true) }}

end spec

end EtcdGrove
end Perennial
