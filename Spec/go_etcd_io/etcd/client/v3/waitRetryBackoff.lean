/-
`clientv3.waitRetryBackoff` (`client/v3/retry_interceptor.go`).

Users: the unary interceptor.

Proof sketch: attempt `0`: no wait. Else the options' backoff function (`optionsAt`: `backoffOk`); a
positive wait: a timer (Perennial's `time.NewTimer`) against `ctx.Done()` (`Context.Done.spec`); the
context done: `contextErrToGRPCErr(ctx.Err())`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean` (an axiom then).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `waitRetryBackoff(ctx, attempt, opts)`: `nil`, or an indefinite error (the context done). -/
def waitRetryBackoff.spec : Prop :=
  ∀ (ctx : GoInterface) (attempt : w64) (p : Loc) (o : RetryOptsM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx ∗ optionsAt p o }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.waitRetryBackoff)) (Val #ctx)) (Val #attempt))
      (Val #p))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ indefCall err }}

end spec

end ClientV3
end EtcdGrove
end Perennial
