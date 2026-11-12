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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `waitRetryBackoff(ctx, attempt, callOpts)` waits (`callOpts.backoffFunc(attempt)`, which
returns: `retryOptsAt`) and returns `nil`, or, if the context is done first, a gRPC status error
(`contextErrToGRPCErr(ctx.Err())`: `status.Error` of the context's error's message,
`clientErrOk`), whose description is the context error's message, never a handler's
(`handlerDescs`: grpc never makes one of those, and `ctxOk` contexts' messages are Go's or
`ctxErrs`' four `clientErrTys` errors'; k8s etcd3 7e-1, restated after an axiom-skill attack). -/
abbrev waitRetryBackoff.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (attempt : w64) (o : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxOk ctx cd ∗
      retryOptsAt o }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.waitRetryBackoff))
      (Val #(GoInterface.ok ctx))) (Val #attempt)) (Val #o))
  {{ (err : GoInterface), RET #err; clientErrOk err ∗
      ⌜err = GoInterface.nil ∨ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ }}

end spec

end EtcdGrove
end Perennial
