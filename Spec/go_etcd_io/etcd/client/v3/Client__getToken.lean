/-
`c.getToken(ctx)` (`client/v3/client.go`, names only; unit P3a): the client's auth part (the
retry interceptor's `refreshToken`): with a token, `c.authTokenBundle.UpdateAuthToken(c.Token)`;
with a user name and password, `c.Auth.Authenticate` (a gRPC call through the same connection, its
retry interceptor included) and the bundle's update.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetryQuiet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.getToken(ctx)` on a client `clientv3.New` built (`retryClientOk`: a bundle whenever a
token) returns `nil` or a client error grpc's `status` accepts (`clientErrOk`: `Authenticate`'s,
through the client's retry interceptor). -/
abbrev Client.getToken.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗
      ctxOk ctx cd }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"getToken"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; clientErrOk err }}

/-- (etcd-io/etcd#21739, pr-verify) **A hypothesis, false**: `c.getToken(ctx)` on a done context
(`ctxErrDone`) returns `nil` or a context status (`ctxCodeErr`). What
`Client.streamClientInterceptor.wp_proof_quiet` needs for the PR's guard of "getToken failed" to
hold back the log. It does not hold: `getToken` returns `c.Auth.Authenticate`'s error, which
`authClient.Authenticate` passes through `ContextError(ctx, err)`; on a done context that turns a
`Canceled`/`DeadlineExceeded` status into `ctx.Err()`, the bare `context.Canceled` (or
`DeadlineExceeded`), whose `status.Code` is `Unknown` (`notes/pr-verify/etcd-21739/`,
`TestStreamInterceptorGetTokenCanceledLogs`). No axiom states it; only the hypothesis of that
proof. -/
abbrev Client.getToken.spec_ctx : Prop :=
  ∀ (c : Loc) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗
      ctxOk ctx cd ∗ ctxErrDone ctx }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"getToken"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; clientErrOk err ∗ (⌜err = GoInterface.nil⌝ ∨ ctxCodeErr err) }}

end spec

end EtcdGrove
end Perennial
