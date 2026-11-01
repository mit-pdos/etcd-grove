/-
`s.doSerialize(ctx, chk, get)` (`v3_server.go`): the auth check, then the read, then the stale-token check.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

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

/-- **`s.doSerialize(ctx, chk, get)`** at a context, with the permission check `chk` (a triple:
on any auth info, an error the gRPC layer can take) and the read `get` (`{G} get() {Q}`): the
request's auth info (`AuthInfoFromCtx`, or an empty one), `chk` of it, `get()`, then the
token's revision against the auth store's (`ErrAuthOldRevision`). Success: `get` ran (`Q`);
failure: an error the gRPC layer can take, and `get` ran or not (`G ∨ Q`). 2026-10-14 (unit A2):
the auth store's reader resource `E.RD`, which `AuthInfoFromCtx` and `chk` take and give back.
2026-10-23 (auth plan A1): `C info`, what a passed `chk` establishes of the auth info it saw (the
permission class of the request's keys, `apply.rangeClass`, `apply.txnClass`); success gives it
of some auth info (the context's, or the empty one).

**In the environment's auth mode** (the auth-mode merge's step 5, 2026-10-29: one spec,
the mode `E.authOn`; the instances at a mode, `specM`, and the mode-off form, `specOff`, are
corollaries in `ModeSpecs.lean`). The mode views (the auth plan's E3s, 2026-10-27): over the request and read
views in the mode (`isServerReqM on`, `isServerReadM on`; `spec` at `on = false`, by definition).
`doSerialize` reads only fields both modes share. With auth on (E3zb, 2026-10-28) the auth info
`chk` passed on is the caller's (`infoBoundM`: the empty one, or bound to the context's token),
given `AuthInfoFromCtx`'s binding with auth on (`AuthInfoFromCtx.spec`). -/
abbrev EtcdServer.doSerialize.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF)
    (C : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info ∗ infoBoundM E.authOn s E (GoInterface.ok ctx) info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}

end spec

end EtcdGrove
end Perennial
