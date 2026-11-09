/-
## `(*Trace).LogIfLong(d)`

**Users.** The request path's deferred loggers (`v3_server.go:133,360,396,1028`). Snippets: `examples/specreq/pkgleaves/trace.go` (`ReqRequestTrace`, `ReqReadLoopTrace`).

**Proof sketch.** If `time.Since(startTime)` exceeds `d`, `LogWithStepThreshold(d / (len(steps)+1))` (the divisor is positive). (`Trace.LogWithStepThreshold.spec`).

**Changes.** From `specs-ref`'s `Trace__LogIfLong.lean`. **Margin.** The trace is consumed: the logger
merges a sub-trace's fields into its steps' with `append`, so the steps' field slices may then
share arrays; every caller logs a trace last.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- **Logs the trace if it took longer than `d`**; the trace consumed. -/
def Trace.LogIfLong.spec : Prop :=
  ∀ (t : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"LogIfLong")) (Val #d))
  {{ RET #(); True }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
