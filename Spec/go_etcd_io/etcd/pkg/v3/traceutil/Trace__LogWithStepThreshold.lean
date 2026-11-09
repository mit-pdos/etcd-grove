/-
## `(*Trace).LogWithStepThreshold(d)`: assumed

**Users.** `LogIfLong`, `LogAllStepsIfLong`, `Log`.

**Assumed** (translated names-only: `logInfo` formats `any` values with `fmt`, reads `math/rand`).
True of the code (`trace.go:208-280`): `logInfo` reads the trace's steps and fields (it writes the
steps' field slices, appending a sub-trace's fields: within the trace's own slices, owned with their
capacities), formats each field with `%v` (`fieldsFmt`: basic values, no methods, immutable) and
the durations, then `t.lg.Info(...)` if `lg` is not nil (`Zap.Logger.Info.spec`). Nothing panics:
`len(steps)` indices are in bounds, `rand.Int31` is total.

**Changes.** From `specs-ref`'s `Trace__LogWithStepThreshold.lean`. **Margin.** The trace is
consumed (see `LogIfLong`).
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

/-- **Logs the trace** (steps longer than `d`); the trace consumed. -/
def Trace.LogWithStepThreshold.spec : Prop :=
  ∀ (t : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"LogWithStepThreshold")) (Val #d))
  {{ RET #(); True }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
