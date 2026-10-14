/-
`s.doSerialize(ctx, chk, get)` (`v3_server.go`): the auth check, then the read, then the stale-token check.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.doSerialize(ctx, chk, get)`** at a context, with the permission check `chk` (a triple:
on any auth info, an error the gRPC layer can take) and the read `get` (`{G} get() {Q}`): the
request's auth info (`AuthInfoFromCtx`, or an empty one), `chk` of it, `get()`, then the
token's revision against the auth store's (`ErrAuthOldRevision`). Success: `get` ran (`Q`);
failure: an error the gRPC layer can take, and `get` ran or not (`G ∨ Q`). 2026-10-14 (unit A2):
the auth store's reader resource `E.RD`, which `AuthInfoFromCtx` and `chk` take and give back. -/
abbrev EtcdServer.doSerialize.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}

end spec

end EtcdGrove
end Perennial
