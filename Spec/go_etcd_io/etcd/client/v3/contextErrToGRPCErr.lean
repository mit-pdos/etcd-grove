/-
`contextErrToGRPCErr(err)` (`client/v3/retry_interceptor.go`; prove-ps2-wrb, 2026-11-22): a done
context's error as a gRPC status error (`errors.Is` against `context.DeadlineExceeded` and
`context.Canceled`, then `status.Error` of the matching code and `err.Error()`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.CtxErrLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `contextErrToGRPCErr(err)`, for a done context's error (`ctxErrLeaf`: a leaf of a context
error's shape whose `Error()` stably returns Go's `"context canceled"` or `"context deadline
exceeded"`), returns a gRPC status error (`status.Error(c, err.Error())`, `c` one of
`DeadlineExceeded`, `Canceled`, `Unknown`, never `OK`): a client error grpc's `status` accepts
(`clientErrOk`), whose description is that message (`descIs`), so no handler's (`notHandlerErr`). -/
abbrev contextErrToGRPCErr.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxErrLeaf err }}
    (App (Val (@! go_etcd_io.etcd.client.v3.contextErrToGRPCErr)) (Val #err))
  {{ (err' : GoInterface), RET #err'; clientErrOk err' ∗ notHandlerErr err' ∗
      ∃ (e : GoInterfaceOk) (m : GoString), ⌜err = GoInterface.ok e ∧
        go_etcd_io.etcd.cache.v3.ctxErrMsg m⌝ ∗ go_etcd_io.etcd.cache.v3.errorMsgIs e m ∗
        go_etcd_io.etcd.cache.v3.descIs err' m }}

end spec

end EtcdGrove
end Perennial
