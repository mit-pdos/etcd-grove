/-
`waitRetryBackoff(ctx, attempt, callOpts)` (`client/v3/retry_interceptor.go`, names only; unit
P3a): the retry interceptor's wait before an attempt, with a timer (`time.NewTimer`, a `select`
on `ctx.Done()` and the timer's channel) and the options' backoff function.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

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

/-- `waitRetryBackoff(ctx, attempt, callOpts)` waits (`callOpts.backoffFunc(attempt)`, which
returns: `retryOptsAt`) and returns `nil`, or, if the context is done first, a gRPC status error
(`contextErrToGRPCErr(ctx.Err())`: `status.Error` of the context's error's message,
`clientErrOk`). -/
abbrev waitRetryBackoff.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (attempt : w64) (o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxOk ctx cd ∗
      retryOptsAt o }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.waitRetryBackoff))
      (Val #(GoInterface.ok ctx))) (Val #attempt)) (Val #o))
  {{ (err : GoInterface), RET #err; clientErrOk err }}

end spec

end EtcdGrove
end Perennial
