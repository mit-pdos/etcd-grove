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

/-- `s.AuthInfoFromCtx(ctx)` at a context, in the caller's auth mode `M`: an auth info (`nil` or one
with its fields, `authInfoOpt`) and an error (the auth store's request side, `isReqAuth`, with the
caller's reader resource `RD`: 2026-10-14, unit A2). With auth on, over the store's request side
with the token binding (`isReqAuthBound`), the auth info is moreover bound to the request's token or
came from the TLS fallback (`ctxBoundOrTLS`; the auth plan's E1/E3zb). The binding is gated by the
mode only because the server's store with auth off comes from `NewAuthStore`'s axiom, which names
the unbound request side (the auth-mode merge, 2026-10-29: `spec` and `boundSpec` one spec, candidate
G of `notes/decisions.md`, "`AuthInfoFromCtx`: one spec, the binding gated by the mode"). With auth
on, the error is moreover `nil` or one of the auth package's error variables (`authErrVarIs`; the
store returns only `ErrInvalidAuthToken`; the lease-expiry plan's E3, 2026-11-05, gated as the
binding is). The context's library values are well formed (`context.libCtxOk`: the store reads its
incoming metadata, and with `ClientCertAuthEnabled` its peer; premise-fixes-8). -/
abbrev EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (cca : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      □ (⌜M.isOn = true⌝ → isReqAuthBound st RD M) ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ (mvcc.txnCtx ctx cd ∨ srvCtxWeak ctx cd) ∗
      context.libCtxOk ctx ∗ RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗ authApplyErrIs err ∗
      □ (⌜M.isOn = true⌝ → ctxBoundOrTLS s M (GoInterface.ok ctx) a) ∗
      □ (⌜M.isOn = true⌝ → authErrVarIs err) }}

end spec

end EtcdGrove
end Perennial
