/-
`s.AuthInfoFromCtx(ctx)` (`v3_server.go`): the request's auth info, from its token, else (with
`ClientCertAuthEnabled`) its TLS certificate. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

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

/-- `s.AuthInfoFromCtx(ctx)` at a context: an auth info (`nil` or one with its fields,
`authInfoOpt`) and an error (the auth store's request side, `isReqAuth`, with the caller's
reader resource `RD`: 2026-10-14, unit A2). -/
abbrev EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (cca : Bool) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ RD }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(GoInterface.ok ctx)))
  {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); RD ∗ authInfoOpt a ∗ applyErrIs err }}

end spec

end EtcdGrove
end Perennial
