# `EtcdServer.AuthInfoFromCtx` (2026-10-29)

The server's `s.AuthInfoFromCtx(ctx)` (`v3_server.go`): the auth info of a request's token (or of the
client's TLS certificate). Two specs of one function, a plain and a "bound" one, merged into one
(the auth-mode merge: `gen-link` links a function by its one `.spec`).

## The first version (two specs)

```lean
abbrev EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (cca : Bool) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ RD }}
    s.AuthInfoFromCtx(ctx)
  {{ (a : Loc) (err : GoInterface), RET (a, err); RD ∗ authInfoOpt a ∗ applyErrIs err }}

abbrev EtcdServer.AuthInfoFromCtx.boundSpec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (cca : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit … ∗ structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      isReqAuthBound st RD M ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ RD }}
    s.AuthInfoFromCtx(ctx)
  {{ (a : Loc) (err : GoInterface), RET (a, err); RD ∗ authInfoOpt a ∗ applyErrIs err ∗
      ctxBoundOrTLS s M (GoInterface.ok ctx) a }}
```

Callers: the request path (`processInternalRaftRequestOnce`, `doSerialize`, through `wpM on`:
`boundSpec` when `on`), the admin guards (`checkMembershipOperationPermission.boundSpec`,
`requireAuthInfo.boundSpec`, v3rpc's `GuardBound`, `WatchBound`, all at `M := E.authMode`), and the
off proofs (`spec`).

## The choice

Two candidates (the spec reviewer recommended G):

- **G**: the binding gated by the caller's mode, `□ (⌜M.isOn = true⌝ → …)` in the pre and the post.
- **U**: ungated. The strongest statement and true of the code (`isReqAuthBound_of_authInv` holds
  at every mode), but with auth off the server's store comes from `NewAuthStore`'s axiom, which
  gives only `isReqAuth`: U needs that axiom strengthened, a trust-base change.

**The user chose G**, and the same gate for the six guards above it (their posts' binding,
`adminOutB`/`authedOutB`), each guard's two specs merged too. The gate is a margin (the axiom's, not
the code's) and the docstring says so.

## The approved spec

```lean
abbrev EtcdServer.AuthInfoFromCtx.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (cca : Bool)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit … ∗ structFieldRef EtcdServer go!"authStore" s ↦□ st ∗ isReqAuth st RD ∗
      □ (⌜M.isOn = true⌝ → isReqAuthBound st RD M) ∗
      srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ cca ∗ mvcc.txnCtx ctx cd ∗ RD }}
    s.AuthInfoFromCtx(ctx)
  {{ (a : Loc) (err : GoInterface), RET (a, err); RD ∗ authInfoOpt a ∗ applyErrIs err ∗
      □ (⌜M.isOn = true⌝ → ctxBoundOrTLS s M (GoInterface.ok ctx) a) }}
```

`M` is the caller's mode (the server's `E.authMode`). Off (`M := .off`) the pre's gated row and the
post's gated row are trivial: `spec` today. On: `boundSpec` today. Why gated: with auth off the
server's store comes from `NewAuthStore`'s axiom (`authStoreKit_off`), which gives `isReqAuth` only;
the binding is true of the code in every mode (`isReqAuthBound_of_authInv` holds at any `M`), but
stating it off needs that axiom strengthened (candidate U).
