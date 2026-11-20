/-
`s.AuthInfoFromCtx(ctx)` (`v3_server.go`): the request's auth info, from its token, else (with
`ClientCertAuthEnabled`) its TLS certificate. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Proof.context.LibKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.AuthInfoFromCtx(ctx)` at a context, in the caller's auth mode `M`, read by a caller holding a
lower bound `n` of the auth store's published index (`auth.authPubLbM`; a caller with none takes
`n := 0`, `auth.authPubLbM_zero`): an auth info (`nil` or one with its fields, `authInfoOpt`) and an
error (the auth store's request side, `isReqAuth`, with the caller's reader resource `RD`: 2026-10-14,
unit A2). With auth on, over the store's request side with the token binding (`isReqAuthBound`), the
auth info is moreover bound to the token `tok` the context carries (`□ (⌜M.isOn⌝ → auth.ctxToken ctx
tok)`, a premise gated by the mode: the store reads the metadata only with auth on; perheap C1a,
2026-11-18, the token a parameter, until then the pure `ctxTokenOf ctx`) or came from the TLS fallback
(`ctxBoundOrTLS`; the auth plan's E1/E3zb). The binding is gated by the mode only because the
server's store with auth off comes from `NewAuthStore`'s axiom, which names the unbound request side
(the auth-mode merge, 2026-10-29, candidate G of `notes/decisions.md`). With auth on, the error is
moreover `nil` or one of the auth package's error variables (`authErrVarIs`; the lease-expiry plan's
E3, 2026-11-05). The context's library values are well formed (`context.libCtxOk`: the TLS fallback
reads its incoming metadata whatever the mode, and with `ClientCertAuthEnabled` its peer;
premise-fixes-8). One spec (perheap C1a merged `spec` and `specLb`, one proof). (auth-guard-completeness
G1, 2026-11-14, `notes/auth-guard-scope.md`, §2.2) With auth on, why the request side gave no
principal (`(nil, nil)`: the flag read `true` at a state no older than `n` and the context carries no
token, or the flag read `false` at such a state, `auth.noPrincipalFrom`; the TLS fallback returns `nil`
only after the store's `(nil, nil)`) and why it failed (`ErrInvalidAuthToken`: the flag read `true` at
such a state and the context carries a token, `auth.tokRefusedFrom`; the token provider's contract says
nothing more of a refused token). (G4, 2026-11-14) A principal comes with the flag read `true` at such a
state (the store's, `store.go:1073`), or the server's TLS fallback is enabled (`srvTLSId`: only that;
a principal from the fallback, `AuthInfoFromTLS`, `v3_server.go:1214`, comes with no flag read:
`nonissues/etcd-auth-old-revision-auth-disabled.md`). -/
abbrev EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (cca : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (n : Nat) (tok : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      □ (⌜M.isOn = true⌝ → isReqAuthBound st RD M) ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ (mvcc.txnCtx ctx cd ∨ srvCtxWeak ctx cd) ∗
      context.libCtxOk ctx ∗ □ (⌜M.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗
      □ auth.authPubLbM M n ∗ RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗ authApplyErrIs err ∗
      □ (⌜M.isOn = true⌝ → ctxBoundOrTLS s M tok a) ∗
      □ (⌜M.isOn = true⌝ → authErrVarIs err) ∗
      □ (⌜M.isOn = true⌝ → ∀ _ : a = null ∧ err = GoInterface.nil,
        auth.noPrincipalFrom M n tok) ∗
      □ (⌜M.isOn = true⌝ → ∀ _ : err ≠ GoInterface.nil,
        auth.authErrOf .invalidAuthToken err ∗ auth.enabledVerdictFrom M n true ∗
          auth.tokRefusedFrom M n tok) ∗
      □ (⌜M.isOn = true⌝ → ∀ _ : a ≠ null, auth.enabledVerdictFrom M n true ∨ srvTLSId s) }}

end spec

end EtcdGrove
end Perennial
